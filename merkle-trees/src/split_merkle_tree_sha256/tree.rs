use rayon::prelude::*;
use rs_merkle::{algorithms::Sha256, Hasher, MerkleProof, MerkleTree};
use std::time::Instant;

pub type Hash = [u8; 32];

#[derive(Clone, Debug)]
pub struct Leaf {
    pub val: Vec<u8>,
}

impl Default for Leaf {
    fn default() -> Self {
        Self { val: vec![0u8; 32] }
    }
}

impl Leaf {
    pub fn hash_leaf(&self) -> Hash {
        Sha256::hash(&self.val)
    }
}

// M is top merkle tree height, N is bottom merkle tree height. H is the sum
// of M+N, because you can't do math in Rust generics like in C++.
pub struct SplitMerkleTree<const M: usize, const N: usize, const H: usize> {
    pub root: Hash,
    pub top_merkle_tree: MerkleTree<Sha256>,
    pub grouped_leaves: Vec<Vec<Leaf>>,
    pub empty_leaf_val: Leaf,
}

pub struct SplitPath<const M: usize, const N: usize> {
    pub top_proof: MerkleProof<Sha256>,
    pub top_leaf_index: usize,
    pub bottom_proof: MerkleProof<Sha256>,
    pub bottom_leaf_index: usize,
}

impl<const M: usize, const N: usize, const H: usize> SplitMerkleTree<M, N, H> {
    // New tree from vector of leaves. `empty_leaf_val` is the default value for leaf of empty tree.
    pub fn from_vec(leaves: Vec<Leaf>, empty_leaf_val: Leaf) -> SplitMerkleTree<M, N, H> {
        let unpadded_leaves_len = leaves.len();
        assert!((1 << (H - 1) <= leaves.len()) && ((1 << H) >= leaves.len()));
        let leaves: Vec<Leaf> = leaves
            .into_iter()
            .chain(
                std::iter::repeat(empty_leaf_val.clone())
                    .take((1usize << H).saturating_sub(unpadded_leaves_len)),
            )
            .take(1usize << H)
            .collect();

        assert_eq!(1 << H, leaves.len());
        assert_eq!(M + N, H);

        let group_size = 1 << N;

        // Group unhashed leaves into buckets of size `group_size`.
        let grouped_leaves: Vec<Vec<Leaf>> = leaves
            .chunks(group_size)
            .map(|chunk| chunk.to_vec())
            .collect();

        // Build bottom merkle trees in parallel and collect their roots
        let bottom_merkle_tree_roots: Vec<Hash> = grouped_leaves
            .par_iter()
            .map(|group: &Vec<Leaf>| {
                let leaf_hashes: Vec<Hash> = group.iter().map(|leaf| leaf.hash_leaf()).collect();
                let subtree = MerkleTree::<Sha256>::from_leaves(&leaf_hashes);
                subtree.root().expect("subtree should have root")
            })
            .collect();

        // Build top merkle tree from bottom tree roots
        let top_merkle_tree = MerkleTree::<Sha256>::from_leaves(&bottom_merkle_tree_roots);
        let root = top_merkle_tree.root().expect("top tree should have root");

        Self {
            root,
            top_merkle_tree,
            grouped_leaves,
            empty_leaf_val,
        }
    }

    // Get siblings given leaf index in bits (MSB first, root-to-leaf order)
    pub fn get_siblings_path(&self, idx_in_bits: Vec<bool>) -> SplitPath<M, N> {
        assert_eq!(idx_in_bits.len(), H);
        let top_tree_bits = idx_in_bits[0..M].to_vec();
        let bottom_tree_bits = idx_in_bits[M..].to_vec();

        let bottom_tree_idx = bits_to_idx(M, top_tree_bits.clone());
        let bottom_tree_leaves = &self.grouped_leaves[bottom_tree_idx];

        // Get top tree proof
        let top_proof = self.top_merkle_tree.proof(&[bottom_tree_idx]);

        // Build bottom tree and get proof
        // println!(
        //     "[DEBUG] Bottom tree leaves: {}, height N={}",
        //     bottom_tree_leaves.len(),
        //     N
        // );
        let bottom_tree_start = Instant::now();
        let leaf_hashes: Vec<Hash> = bottom_tree_leaves
            .iter()
            .map(|leaf| leaf.hash_leaf())
            .collect();
        let bottom_tree = MerkleTree::<Sha256>::from_leaves(&leaf_hashes);
        let bottom_tree_build_time = bottom_tree_start.elapsed();
        // println!(
        //     "[DEBUG] Bottom tree construction: {:?}",
        //     bottom_tree_build_time
        // );

        let leaf_idx_in_bottom = bits_to_idx(N, bottom_tree_bits);
        let bottom_proof = bottom_tree.proof(&[leaf_idx_in_bottom]);

        SplitPath {
            top_proof,
            top_leaf_index: bottom_tree_idx,
            bottom_proof,
            bottom_leaf_index: leaf_idx_in_bottom,
        }
    }

    // Verify a leaf against the split tree
    pub fn verify(&self, idx_in_bits: Vec<bool>, leaf: &Leaf, proof: &SplitPath<M, N>) -> bool {
        assert_eq!(idx_in_bits.len(), H);

        let leaf_hash = leaf.hash_leaf();

        // Compute the bottom tree root from the proof
        let bottom_tree_size = 1 << N;
        let bottom_root = match proof.bottom_proof.root(
            &[proof.bottom_leaf_index],
            &[leaf_hash],
            bottom_tree_size,
        ) {
            Ok(root) => root,
            Err(_) => return false,
        };

        // Verify top proof using the bottom root as the leaf
        let top_tree_size = 1 << M;
        proof.top_proof.verify(
            self.root,
            &[proof.top_leaf_index],
            &[bottom_root],
            top_tree_size,
        )
    }

    // Returns the number of bytes used by the tree to store the hashes.
    // Note that this is additional bytes, the contents of the tree (e.g. grouped_leaves) don't count.
    pub fn additional_storage_used(&self) -> usize {
        // rs_merkle stores all nodes internally
        // For a tree with 2^M leaves, it stores 2^(M+1) - 1 nodes
        // Each node is 32 bytes (SHA256)
        let top_tree_nodes = (1 << (M + 1)) - 1;
        top_tree_nodes * 32
    }
}

// Convert a path (MSB-first, root-to-leaf) to a usize index, matching `idx_to_bits` conventions.
pub fn bits_to_idx(depth: usize, mut bits: Vec<bool>) -> usize {
    // Pad with zeros if shorter; truncate higher-order bits if longer than depth.
    if bits.len() < depth {
        let mut padding = vec![false; depth - bits.len()];
        padding.append(&mut bits);
        bits = padding;
    } else if bits.len() > depth {
        bits = bits[bits.len() - depth..].to_vec();
    }

    bits.reverse(); // now least-significant bit first

    let mut idx = 0usize;
    for (i, bit) in bits.iter().enumerate() {
        if *bit {
            idx |= 1usize << i;
        }
    }
    idx
}

// Convert index to bits (MSB-first, root-to-leaf order)
pub fn idx_to_bits(depth: usize, idx: usize) -> Vec<bool> {
    let mut path: Vec<bool> = vec![];
    let mut remaining = idx;
    for _ in 0..depth {
        path.push((remaining & 1) == 1);
        remaining >>= 1;
    }
    path.reverse();
    path
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_tree_path() {
        const M: usize = 2;
        const N: usize = 2;
        const H: usize = M + N; // total depth
        const TOTAL_LEAVES: usize = 1 << H; // 16 leaves

        let empty_leaf_val = Leaf::default();

        let leaves: Vec<Leaf> = (0..TOTAL_LEAVES)
            .map(|i| Leaf {
                val: vec![i as u8; 32],
            })
            .collect();

        let split_tree: SplitMerkleTree<M, N, H> =
            SplitMerkleTree::from_vec(leaves.clone(), empty_leaf_val.clone());

        for i in 0..TOTAL_LEAVES {
            let idx_bits = idx_to_bits(H, i);
            let proof = split_tree.get_siblings_path(idx_bits.clone());
            assert!(split_tree.verify(idx_bits.clone(), &leaves[i], &proof));
        }
    }

    #[test]
    fn test_bits_conversion() {
        for i in 0..16 {
            let bits = idx_to_bits(4, i);
            let recovered = bits_to_idx(4, bits);
            assert_eq!(i, recovered);
        }
    }
}
