use crate::hash::vanilla::hash;
use ff::{PrimeField, PrimeFieldBits};
use neptune::poseidon::PoseidonConstants;
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::{Arity, Strength};
use std::collections::HashMap;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct Leaf<F: PrimeField + PrimeFieldBits, A: Arity<F>> {
    pub val: Vec<F>,
    pub _arity: PhantomData<A>,
}

impl<F: PrimeField + PrimeFieldBits, A: Arity<F>> Default for Leaf<F, A> {
    fn default() -> Self {
        Self {
            val: vec![F::ZERO],
            _arity: PhantomData,
        }
    }
}

impl<F, A> Leaf<F, A>
where
    F: PrimeField + PrimeFieldBits,
    A: Arity<F>,
{
    pub fn hash_leaf(&self, p: &PoseidonConstants<F, A>) -> F {
        hash::<F, A>(self.val.clone(), p)
    }
}

#[derive(Clone, Debug)]
pub struct MerkleTree<F: PrimeField + PrimeFieldBits, const N: usize, AL: Arity<F>, AN: Arity<F>> {
    pub root: F,
    pub hash_db: HashMap<String, (F, F)>,
    pub leaf_hash_params: PoseidonConstants<F, AL>,
    pub node_hash_params: PoseidonConstants<F, AN>,
}

impl<F: PrimeField + PrimeFieldBits, const N: usize, AL: Arity<F>, AN: Arity<F>>
    MerkleTree<F, N, AL, AN>
{
    // Create a new tree. `empty_leaf_val` is the default value for leaf of empty tree.
    pub fn new(empty_leaf_val: Leaf<F, AL>) -> MerkleTree<F, N, AL, AN> {
        let mut hash_db = HashMap::<String, (F, F)>::new();
        let leaf_hash_params = Sponge::<F, AL>::api_constants(Strength::Standard);
        let node_hash_params = Sponge::<F, AN>::api_constants(Strength::Standard);
        let mut cur_hash = Leaf::<F, AL>::hash_leaf(&empty_leaf_val, &leaf_hash_params);
        for _ in 0..N {
            let val = (cur_hash.clone(), cur_hash.clone());
            cur_hash = hash(vec![cur_hash.clone(), cur_hash.clone()], &node_hash_params);
            hash_db.insert(format!("{:?}", cur_hash.clone()), val);
        }
        Self {
            root: cur_hash,
            hash_db: hash_db,
            leaf_hash_params: leaf_hash_params,
            node_hash_params: node_hash_params,
        }
    }

    // New tree from vector of leaves. `empty_leaf_val` is the default value for leaf of empty tree.
    pub fn from_vec(
        leaves: Vec<Leaf<F, AL>>,
        empty_leaf_val: Leaf<F, AL>,
    ) -> MerkleTree<F, N, AL, AN> {
        let mut hash_db = HashMap::<String, (F, F)>::new();
        let leaf_hash_params = Sponge::<F, AL>::api_constants(Strength::Standard);
        let node_hash_params = Sponge::<F, AN>::api_constants(Strength::Standard);
        // Insert all the leaves. We keep a list of any outstanding "left hash" on each level
        let mut left_hashes: Vec<Option<F>> = Vec::new();
        left_hashes.resize(N + 1, None);
        for i in 0..leaves.len() {
            let mut right_hash = Leaf::<F, AL>::hash_leaf(&leaves[i], &leaf_hash_params);
            let mut level = 0;
            // Hash upwards until there is no left hash
            while level < N {
                match left_hashes[level] {
                    Some(left_hash) => {
                        // combine left hash with right hash
                        let val = (left_hash.clone(), right_hash.clone());
                        right_hash = hash(
                            vec![left_hash.clone(), right_hash.clone()],
                            &node_hash_params,
                        );
                        hash_db.insert(format!("{:?}", right_hash.clone()), val);
                        left_hashes[level] = None;
                    }
                    None => {
                        break;
                    }
                }
                level += 1;
            }
            left_hashes[level] = Some(right_hash);
        }
        // Insert remaining empty leaves
        let mut empty_hash = Leaf::<F, AL>::hash_leaf(&empty_leaf_val, &leaf_hash_params);
        let mut right_hash = empty_hash.clone();
        for level in 0..N {
            // compute empty_hash for next level
            let val = (empty_hash.clone(), empty_hash.clone());
            empty_hash = hash(
                vec![empty_hash.clone(), empty_hash.clone()],
                &node_hash_params,
            );
            hash_db.insert(format!("{:?}", empty_hash.clone()), val);

            match left_hashes[level] {
                Some(left_hash) => {
                    // combine left hash with right hash
                    let val = (left_hash.clone(), right_hash.clone());
                    let next_hash = hash(
                        vec![left_hash.clone(), right_hash.clone()],
                        &node_hash_params,
                    );
                    hash_db.insert(format!("{:?}", next_hash.clone()), val);
                    match left_hashes[level + 1] {
                        Some(_) => {
                            right_hash = next_hash.clone();
                        }
                        None => {
                            left_hashes[level + 1] = Some(next_hash);
                            // right hash becomes the empty hash for the next level
                            right_hash = empty_hash.clone();
                        }
                    }
                }
                None => {
                    // right hash becomes the empty hash for the next level
                    right_hash = empty_hash.clone();
                }
            }
        }
        Self {
            root: left_hashes[N].unwrap_or(empty_hash),
            hash_db: hash_db,
            leaf_hash_params: leaf_hash_params,
            node_hash_params: node_hash_params,
        }
    }

    pub fn insert(&mut self, mut idx_in_bits: Vec<bool>, val: &Leaf<F, AL>) {
        let mut siblings = self.get_siblings_path(idx_in_bits.clone()).siblings;

        // Reverse since path was from root to leaf but I am going leaf to root
        idx_in_bits.reverse();
        let mut cur_hash = Leaf::<F, AL>::hash_leaf(val, &self.leaf_hash_params);

        // Iterate over the bits
        for d in idx_in_bits {
            let sibling = siblings.pop().unwrap();
            let (l, r) = if d == false {
                // leaf falls on the left side
                (cur_hash, sibling)
            } else {
                // leaf falls on the right side
                (sibling, cur_hash)
            };
            let val = (l, r);
            cur_hash = hash(vec![l.clone(), r.clone()], &self.node_hash_params);
            self.hash_db.insert(format!("{:?}", cur_hash.clone()), val);
        }

        self.root = cur_hash;
    }

    // Get siblings given leaf index index
    pub fn get_siblings_path(&self, idx_in_bits: Vec<bool>) -> Path<F, N, AL, AN> {
        let mut cur_node = self.root;
        let mut siblings = Vec::<F>::new();

        let mut children;
        for d in idx_in_bits {
            children = self
                .hash_db
                .get(&format!("{:?}", cur_node.clone()))
                .unwrap();
            if d == false {
                // leaf falls on the left side
                cur_node = children.0;
                siblings.push(children.1);
            } else {
                // leaf falls on the right side
                cur_node = children.1;
                siblings.push(children.0);
            }
        }
        Path {
            siblings: siblings,
            leaf_hash_params: self.leaf_hash_params.clone(),
            node_hash_params: self.node_hash_params.clone(),
        }
    }

    // Returns the number of bytes used by the tree to store the hashes.
    // Note that this is additional bytes, the contents of the tree don't count.
    // Likewise, root is double counted in hash_db so that is fine.
    pub fn additional_storage_used(&self) -> usize {
        const POSEIDON_HASH_SIZE: usize = 32;
        self.hash_db.len() * POSEIDON_HASH_SIZE
    }
}

pub fn idx_to_bits<F: PrimeField + PrimeFieldBits>(depth: usize, idx: F) -> Vec<bool> {
    let mut path: Vec<bool> = vec![];
    for d in idx.to_le_bits() {
        if path.len() >= depth {
            break;
        }

        if d == true {
            path.push(true)
        } else {
            path.push(false)
        }
    }

    while path.len() != depth {
        path.push(false);
    }

    path.reverse();
    path
}

#[derive(Clone, Debug)]
pub struct Path<F, const N: usize, AL, AN>
where
    F: PrimeField + PrimeFieldBits,
    AL: Arity<F>,
    AN: Arity<F>,
{
    pub siblings: Vec<F>, // siblings from root to leaf
    pub leaf_hash_params: PoseidonConstants<F, AL>,
    pub node_hash_params: PoseidonConstants<F, AN>,
}

impl<'a, F: PrimeField + PrimeFieldBits, const N: usize, AL: Arity<F>, AN: Arity<F>>
    Path<F, N, AL, AN>
{
    pub fn compute_root(&self, mut idx_in_bits: Vec<bool>, val: &Leaf<F, AL>) -> F {
        assert_eq!(self.siblings.len(), N);
        idx_in_bits.reverse();

        let mut cur_hash = Leaf::<F, AL>::hash_leaf(val, &self.leaf_hash_params);

        for (i, sibling) in self.siblings.clone().into_iter().rev().enumerate() {
            let (l, r) = if idx_in_bits[i] == false {
                // leaf falls on the left side
                (cur_hash, sibling)
            } else {
                // leaf falls on the right side
                (sibling, cur_hash)
            };
            cur_hash = hash(vec![l.clone(), r.clone()], &self.node_hash_params);
        }
        cur_hash
    }

    pub fn verify(&self, idx_in_bits: Vec<bool>, val: &Leaf<F, AL>, root: F) -> bool {
        let computed_root = self.compute_root(idx_in_bits, val);
        computed_root == root
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;
    use generic_array::typenum::{U1, U2};
    use pasta_curves::Fp;

    #[test]
    fn test_tree_insert() {
        let mut rng = rand::thread_rng();
        const HEIGHT: usize = 32;
        let empty_leaf_val = Leaf::default();

        let mut tree: MerkleTree<Fp, HEIGHT, U1, U2> = MerkleTree::new(empty_leaf_val);

        let test_cases: u64 = 100;

        for i in 0..test_cases {
            let idx = Fp::from(i);
            let idx_in_bits = idx_to_bits(HEIGHT, idx);
            let val = Leaf {
                val: vec![Fp::random(&mut rng)],
                _arity: PhantomData,
            };

            let path = tree.get_siblings_path(idx_in_bits.clone());
            assert!(!path.verify(idx_in_bits.clone(), &val, tree.root));
            tree.insert(idx_in_bits.clone(), &val);
            let new_path = tree.get_siblings_path(idx_in_bits.clone());
            assert!(new_path.verify(idx_in_bits.clone(), &val, tree.root));
        }
    }
}
