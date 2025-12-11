use crate::hash::vanilla::hash;
use crate::vanilla_tree::tree::{idx_to_bits, Leaf, MerkleTree, Path};
use ff::{PrimeField, PrimeFieldBits};
use neptune::poseidon::PoseidonConstants;
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::{Arity, Strength};
use std::marker::PhantomData;

// AL: Leaf Arity, AN: Arity for internal nodes, AL2: Arity for sponge application to compress large leaves.
// LEAF_SIZE: the size of each leaf.
#[derive(Clone, Debug)]
pub struct LargeLeafMerkleTree<
    F: PrimeField + PrimeFieldBits,
    const LEAF_SIZE: usize,
    const HEIGHT: usize,
    AL: Arity<F>,
    AL2: Arity<F>,
    AN: Arity<F>,
> {
    pub merkle_tree: MerkleTree<F, HEIGHT, AL, AN>,
    pub grouped_leaves: Vec<Vec<F>>,
    pub leaf_hashes: Vec<F>,
    pub _large_leaf_marker: PhantomData<AL2>,
}

// Wrapper class to store the arity AL2 and have a different verification logic.
#[derive(Clone, Debug)]
pub struct LargeLeafPath<
    F: PrimeField + PrimeFieldBits,
    const LEAF_SIZE: usize,
    const HEIGHT: usize,
    AL: Arity<F>,
    AL2: Arity<F>,
    AN: Arity<F>,
> {
    pub native_path: Path<F, HEIGHT, AL, AN>,
    pub leaf_contents: Vec<F>, // The other parts of the leaf.
    pub _large_leaf_marker: PhantomData<AL2>,
}

impl<
        F: PrimeField + PrimeFieldBits,
        const LEAF_SIZE: usize,
        const HEIGHT: usize,
        AL: Arity<F>,
        AL2: Arity<F>,
        AN: Arity<F>,
    > LargeLeafMerkleTree<F, LEAF_SIZE, HEIGHT, AL, AL2, AN>
{
    // New tree from vector of Field elements. `empty_leaf_val` is the default value for leaf of empty tree.
    // The F-val will also be used to pad out blocks of leaves.
    pub fn from_vec(
        leaves: Vec<F>,
        empty_leaf_val: Leaf<F, AL>,
    ) -> LargeLeafMerkleTree<F, LEAF_SIZE, HEIGHT, AL, AL2, AN> {
        let empty_leaf_felt = empty_leaf_val
            .val
            .get(0)
            .cloned()
            .unwrap_or_else(|| F::ZERO);
        // Group unhashed leaves into buckets of size `group_size`.
        let grouped_leaves: Vec<Vec<F>> = leaves
            .chunks(LEAF_SIZE)
            .map(|chunk| {
                let mut v = chunk.to_vec();
                let pad_val = empty_leaf_felt.clone();
                if v.len() < LEAF_SIZE {
                    v.resize(LEAF_SIZE, pad_val);
                }
                v
            })
            .collect();

        let large_leaf_hash_params = Sponge::<F, AL2>::api_constants(Strength::Standard);
        let leaf_hashes: Vec<F> = grouped_leaves
            .clone()
            .iter()
            .map(|group| hash(group.to_vec(), &large_leaf_hash_params))
            .collect();

        let hashes_as_leaves: Vec<Leaf<F, AL>> = leaf_hashes
            .iter()
            .map(|hash| Leaf {
                val: vec![hash.clone()],
                _arity: PhantomData,
            })
            .collect();
        let merkle_tree: MerkleTree<F, HEIGHT, AL, AN> =
            MerkleTree::from_vec(hashes_as_leaves, empty_leaf_val.clone());

        Self {
            merkle_tree: merkle_tree,
            leaf_hashes: leaf_hashes,
            grouped_leaves: grouped_leaves,
            _large_leaf_marker: PhantomData,
        }
    }

    // Get siblings given leaf index
    pub fn get_siblings_path(
        &self,
        idx_in_bits: Vec<bool>,
    ) -> LargeLeafPath<F, LEAF_SIZE, HEIGHT, AL, AL2, AN> {
        let long_path_length = ((LEAF_SIZE * (1 << HEIGHT)) as f64).log2().ceil() as usize;
        let leaf_idx = bits_to_idx(long_path_length, idx_in_bits);
        let large_leaf_idx = leaf_idx / LEAF_SIZE;
        let large_leaf_idx_in_bits = idx_to_bits(HEIGHT, F::from(large_leaf_idx as u64));

        LargeLeafPath {
            native_path: self.merkle_tree.get_siblings_path(large_leaf_idx_in_bits),
            leaf_contents: self.grouped_leaves[large_leaf_idx].clone(),
            _large_leaf_marker: PhantomData,
        }
    }

    pub fn verify(
        &self,
        idx_in_bits: Vec<bool>,
        leaf: F,
        proof: &LargeLeafPath<F, LEAF_SIZE, HEIGHT, AL, AL2, AN>,
    ) -> bool {
        let large_leaf_hash_params = Sponge::<F, AL2>::api_constants(Strength::Standard);
        let leaf_hash = hash(proof.leaf_contents.clone(), &large_leaf_hash_params);

        let long_path_length = ((LEAF_SIZE * (1 << HEIGHT)) as f64).log2().ceil() as usize;
        let leaf_idx = bits_to_idx(long_path_length, idx_in_bits);
        let index_in_leaf = leaf_idx % LEAF_SIZE;
        assert_eq!(leaf, proof.leaf_contents[index_in_leaf]);

        let large_leaf_idx = leaf_idx / LEAF_SIZE;
        let large_leaf_idx_in_bits = idx_to_bits(HEIGHT, F::from(large_leaf_idx as u64));
        let leaf = Leaf {
            val: vec![leaf_hash],
            _arity: PhantomData,
        };

        proof
            .native_path
            .verify(large_leaf_idx_in_bits, &leaf, self.merkle_tree.root)
    }

    // Returns the number of bytes used by the tree to store the hashes.
    // Note that this is additional bytes, the contents of the tree don't count.
    pub fn additional_storage_used(&self) -> usize {
        const POSEIDON_HASH_SIZE: usize = 32;
        self.merkle_tree.additional_storage_used() + self.leaf_hashes.len() * POSEIDON_HASH_SIZE
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
    fn test_large_leaf_tree_path() {
        let mut rng = rand::thread_rng();
        const HEIGHT: usize = 5; // total depth
        const LEAF_SIZE: usize = 10; // 16 leaves
        let TOTAL_LEAVES = LEAF_SIZE * (1 << HEIGHT);
        let long_path_length = ((LEAF_SIZE * (1 << HEIGHT)) as f64).log2().ceil() as usize;

        let empty_leaf_val = Leaf::default();
        let leaves: Vec<Fp> = (0..TOTAL_LEAVES).map(|_| Fp::random(&mut rng)).collect();

        let tree: LargeLeafMerkleTree<Fp, LEAF_SIZE, HEIGHT, U1, U1, U2> =
            LargeLeafMerkleTree::from_vec(leaves.clone(), empty_leaf_val.clone());

        for i in 0..TOTAL_LEAVES {
            let idx_bits = idx_to_bits(long_path_length, Fp::from(i as u64));
            let proof = tree.get_siblings_path(idx_bits.clone());
            assert!(tree.verify(idx_bits.clone(), leaves[i], &proof));
        }
    }
}
