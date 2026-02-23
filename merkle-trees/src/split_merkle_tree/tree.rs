use crate::vanilla_tree::tree::{Leaf, MerkleTree, Path};
use ff::{PrimeField, PrimeFieldBits};
use neptune::Arity;
use rayon::prelude::*;
use std::marker::PhantomData;
use std::time::Instant;

// M is top merkle tree size, N is bottom merkle tree size. H is the sum
// of M+N, because you can't do math in Rust generics like in C++.
#[derive(Clone, Debug)]
pub struct SplitMerkleTree<
    F: PrimeField + PrimeFieldBits,
    const M: usize,
    const N: usize,
    const H: usize,
    AL: Arity<F>,
    AN: Arity<F>,
> {
    pub root: F,
    pub top_merkle_tree: MerkleTree<F, M, AL, AN>,
    pub grouped_leaves: Vec<Vec<Leaf<F, AL>>>,
}

#[derive(Clone, Debug)]
pub struct SplitPath<
    F: PrimeField + PrimeFieldBits,
    const M: usize,
    const N: usize,
    AL: Arity<F>,
    AN: Arity<F>,
> {
    pub top_path: Path<F, M, AL, AN>,
    pub bottom_path: Path<F, N, AL, AN>,
}

impl<
        F: PrimeField + PrimeFieldBits + Send + Sync,
        const M: usize,
        const N: usize,
        const H: usize,
        AL: Arity<F> + Send + Sync,
        AN: Arity<F> + Send + Sync,
    > SplitMerkleTree<F, M, N, H, AL, AN>
{
    // New tree from vector of leaves. `empty_leaf_val` is the default value for leaf of empty tree.
    pub fn from_vec(
        leaves: Vec<Leaf<F, AL>>,
        empty_leaf_val: Leaf<F, AL>,
    ) -> SplitMerkleTree<F, M, N, H, AL, AN> {
        let unpadded_leaves_len = leaves.len();
        assert!((1 << (H - 1) <= leaves.len()) && ((1 << H) >= leaves.len()));
        let leaves = leaves
            .into_iter()
            .chain(
                std::iter::repeat(empty_leaf_val.clone())
                    .take((1usize << H).saturating_sub(unpadded_leaves_len)),
            )
            .take(1usize << H)
            .collect::<Vec<_>>();

        assert_eq!(1 << H, leaves.len());
        assert_eq!(M + N, H);

        let group_size = 1 << N;

        // Group unhashed leaves into buckets of size `group_size`.
        let grouped_leaves: Vec<Vec<Leaf<F, AL>>> = leaves
            .chunks(group_size)
            .map(|chunk| chunk.to_vec())
            .collect();

        let bottom_merkle_tree_roots: Vec<_> = grouped_leaves
            .par_iter()
            .map(|group: &Vec<Leaf<F, AL>>| {
                let subtree: MerkleTree<F, N, AL, AN> =
                    MerkleTree::from_vec(group.clone(), empty_leaf_val.clone());
                Leaf {
                    val: vec![subtree.root],
                    _arity: PhantomData,
                }
            })
            .collect();

        let top_merkle_tree: MerkleTree<F, M, AL, AN> =
            MerkleTree::from_vec(bottom_merkle_tree_roots.clone(), empty_leaf_val.clone());

        Self {
            root: top_merkle_tree.root,
            top_merkle_tree: top_merkle_tree,
            grouped_leaves: grouped_leaves,
        }
    }

    // Get siblings given leaf index index
    pub fn get_siblings_path(&self, idx_in_bits: Vec<bool>) -> SplitPath<F, M, N, AL, AN> {
        assert_eq!(idx_in_bits.len(), H);
        let top_tree_bits = idx_in_bits[0..M].to_vec();
        let bottom_tree_bits = idx_in_bits[M..].to_vec();

        let bottom_tree_idx = bits_to_idx(M, top_tree_bits.clone());
        let bottom_tree_leaves = self.grouped_leaves[bottom_tree_idx].clone();

        let top_tree_path = self.top_merkle_tree.get_siblings_path(top_tree_bits);

        println!("[DEBUG] Bottom tree leaves: {}, height N={}", bottom_tree_leaves.len(), N);
        let bottom_tree_start = Instant::now();
        let bottom_tree =
            MerkleTree::<F, N, AL, AN>::from_vec(bottom_tree_leaves, Leaf::<F, AL>::default());
        let bottom_tree_build_time = bottom_tree_start.elapsed();
        println!("[DEBUG] Bottom tree construction: {:?}", bottom_tree_build_time);

        let bottom_tree_path = bottom_tree.get_siblings_path(bottom_tree_bits);

        SplitPath {
            top_path: top_tree_path,
            bottom_path: bottom_tree_path,
        }
    }

    // Verify a leaf against the split tree, respecting the extra leaf hash on the top tree.
    pub fn verify(
        &self,
        idx_in_bits: Vec<bool>,
        leaf: &Leaf<F, AL>,
        proof: &SplitPath<F, M, N, AL, AN>,
    ) -> bool {
        assert_eq!(idx_in_bits.len(), H);
        let top_tree_bits = idx_in_bits[0..M].to_vec();
        let bottom_tree_bits = idx_in_bits[M..].to_vec();

        // First compute the bottom root using the provided bottom path.
        let bottom_root = proof.bottom_path.compute_root(bottom_tree_bits, leaf);

        // Treat the bottom root as the single-field leaf of the top tree.
        let top_leaf = Leaf {
            val: vec![bottom_root],
            _arity: PhantomData,
        };

        proof.top_path.verify(top_tree_bits, &top_leaf, self.root)
    }

    // Returns the number of bytes used by the tree to store the hashes.
    // Note that this is additional bytes, the contents of the tree (e.g. grouped_leaves) don't count.
    pub fn additional_storage_used(&self) -> usize {
        self.top_merkle_tree.additional_storage_used()
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vanilla_tree::tree::idx_to_bits;
    use ff::Field;
    use generic_array::typenum::{U1, U2};
    use pasta_curves::Fp;
    use std::marker::PhantomData;

    #[test]
    fn test_split_tree_path() {
        let mut rng = rand::thread_rng();
        const M: usize = 2;
        const N: usize = 2;
        const H: usize = M + N; // total depth
        const TOTAL_LEAVES: usize = 1 << H; // 16 leaves

        let empty_leaf_val = Leaf::default();

        let leaves: Vec<Leaf<Fp, U1>> = (0..TOTAL_LEAVES)
            .map(|_| Leaf {
                val: vec![Fp::random(&mut rng)],
                _arity: PhantomData,
            })
            .collect();

        let split_tree: SplitMerkleTree<Fp, M, N, H, U1, U2> =
            SplitMerkleTree::from_vec(leaves.clone(), empty_leaf_val.clone());

        for i in 0..TOTAL_LEAVES {
            let idx_bits = idx_to_bits(H, Fp::from(i as u64));
            let proof = split_tree.get_siblings_path(idx_bits.clone());
            assert!(split_tree.verify(idx_bits.clone(), &leaves[i], &proof));
        }
    }
}
