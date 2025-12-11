use crate::hash::circuit::hash_circuit;
use bellpepper::gadgets::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{PrimeField, PrimeFieldBits};
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::{Arity, Strength};

pub fn path_computed_root<
    F: PrimeField + PrimeFieldBits,
    AL: Arity<F>,
    AL2: Arity<F>,
    AN: Arity<F>,
    const LEAF_SIZE: usize,
    const HEIGHT: usize,
    CS: ConstraintSystem<F>,
>(
    cs: &mut CS,
    val_var: Vec<AllocatedNum<F>>,
    mut idx_var: Vec<AllocatedBit>,
    siblings_var: Vec<AllocatedNum<F>>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    assert_eq!(siblings_var.len(), HEIGHT);

    let node_hash_params = Sponge::<F, AN>::api_constants(Strength::Standard);
    let leaf_hash_params = Sponge::<F, AL>::api_constants(Strength::Standard);
    let leaf_hash_2_params = Sponge::<F, AL2>::api_constants(Strength::Standard);
    // Hash the leaf.
    let mut cur_hash_var = hash_circuit(
        &mut cs.namespace(|| "hash num -2 :"),
        val_var,
        &leaf_hash_2_params,
    )
    .unwrap();

    // Hash bottom root to make it a leaf for the top tree.
    // This hash is not necessary but givs us compatibility with existing merkle tree code.
    let mut cur_hash_var = hash_circuit(
        &mut cs.namespace(|| "hash num -1 :"),
        vec![cur_hash_var],
        &leaf_hash_params,
    )
    .unwrap();

    idx_var.reverse(); // Going from leaf to root

    for (i, sibling) in siblings_var.into_iter().rev().enumerate() {
        let (lc, rc) = AllocatedNum::conditionally_reverse(
            &mut cs.namespace(|| format!("rev num {} :", i)),
            &cur_hash_var,
            &sibling,
            &Boolean::from(idx_var[i].clone()),
        )
        .unwrap();
        cur_hash_var = hash_circuit(
            &mut cs.namespace(|| format!("hash num {} :", i)),
            vec![lc, rc],
            &node_hash_params,
        )
        .unwrap();
    }

    Ok(cur_hash_var)
}

pub fn path_verify_circuit<
    F: PrimeField + PrimeFieldBits,
    AL: Arity<F>,
    AL2: Arity<F>,
    AN: Arity<F>,
    const LEAF_SIZE: usize,
    const HEIGHT: usize,
    CS: ConstraintSystem<F>,
>(
    cs: &mut CS,
    root_var: AllocatedNum<F>,
    val_var: Vec<AllocatedNum<F>>,
    mut idx_var: Vec<AllocatedBit>,
    siblings_var: Vec<AllocatedNum<F>>,
) -> Result<AllocatedBit, SynthesisError> {
    assert_eq!(siblings_var.len(), HEIGHT);
    let node_hash_params = Sponge::<F, AN>::api_constants(Strength::Standard);
    let leaf_hash_params = Sponge::<F, AL>::api_constants(Strength::Standard);
    let leaf_hash_2_params = Sponge::<F, AL2>::api_constants(Strength::Standard);
    let mut cur_hash_var = hash_circuit(
        &mut cs.namespace(|| "hash num -2 :"),
        val_var,
        &leaf_hash_2_params,
    )
    .unwrap();

    // Unnecessary hash for compatibility reasons.
    let mut cur_hash_var = hash_circuit(
        &mut cs.namespace(|| "hash num -1 :"),
        vec![cur_hash_var],
        &leaf_hash_params,
    )
    .unwrap();

    idx_var.reverse(); // Going from leaf to root

    for (i, sibling) in siblings_var.into_iter().rev().enumerate() {
        let (lc, rc) = AllocatedNum::conditionally_reverse(
            &mut cs.namespace(|| format!("rev num {} :", i)),
            &cur_hash_var,
            &sibling,
            &Boolean::from(idx_var[i].clone()),
        )
        .unwrap();
        cur_hash_var = hash_circuit(
            &mut cs.namespace(|| format!("hash num {} :", i)),
            vec![lc, rc],
            &node_hash_params,
        )
        .unwrap();
    }

    let is_valid = AllocatedBit::alloc(
        cs.namespace(|| "is member"),
        Some(root_var.get_value() == cur_hash_var.get_value()),
    )?;

    cs.enforce(
        || "constraint is_valid",
        |lc| lc + is_valid.get_variable(),
        |lc| lc + root_var.get_variable() - cur_hash_var.get_variable(),
        |lc| lc,
    );

    Ok(is_valid)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::large_leaf_merkle_tree::tree::LargeLeafMerkleTree;
    use crate::vanilla_tree::tree::{idx_to_bits, Leaf, MerkleTree};
    use bellpepper_core::test_cs::TestConstraintSystem;
    use ff::Field;
    use generic_array::typenum::{U1, U2};
    use pasta_curves::Fp;
    use rand::Rng;
    use std::marker::PhantomData;

    #[test]
    fn test_large_leaf_tree_path_verify_circuit() {
        let mut rng = rand::thread_rng();
        const HEIGHT: usize = 8;
        const LEAF_SIZE: usize = 1 << 4;
        let leaves_len = (1 << HEIGHT) * LEAF_SIZE;
        let long_path_length = ((leaves_len) as f64).log2().ceil() as usize;
        let random_leaves: Vec<Fp> = (0..leaves_len).map(|_| Fp::random(&mut rng)).collect();
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut tree: LargeLeafMerkleTree<Fp, LEAF_SIZE, HEIGHT, U1, U1, U2> =
            LargeLeafMerkleTree::from_vec(random_leaves.clone(), Leaf::default());

        let test_cases: u64 = 10;

        for j in 0..test_cases {
            let idx_raw: u64 = rng.gen_range(0..leaves_len as u64);
            let idx = Fp::from(idx_raw);
            let idx_in_bits = idx_to_bits(long_path_length, idx);
            let leaf = random_leaves[idx_raw as usize].clone();

            let path = tree.get_siblings_path(idx_in_bits.clone());
            let long_leaf = path.leaf_contents;
            let large_leaf_idx = (idx_raw as usize) / LEAF_SIZE;
            let large_leaf_idx_in_bits = idx_to_bits(HEIGHT, Fp::from(large_leaf_idx as u64));

            // Allocating all variables
            let root_var: AllocatedNum<Fp> =
                AllocatedNum::alloc_input(cs.namespace(|| format!("root {}", j)), || {
                    Ok(tree.merkle_tree.root)
                })
                .unwrap();
            let val_var: Vec<AllocatedNum<Fp>> = long_leaf
                .clone()
                .into_iter()
                .enumerate()
                .map(|(i, s)| {
                    AllocatedNum::alloc(cs.namespace(|| format!("{} : leaf vec {}", j, i)), || {
                        Ok(s)
                    })
                })
                .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
                .unwrap();
            let siblings_var: Vec<AllocatedNum<Fp>> = path
                .native_path
                .siblings
                .into_iter()
                .enumerate()
                .map(|(i, s)| {
                    AllocatedNum::alloc(cs.namespace(|| format!("{} : sibling {}", j, i)), || Ok(s))
                })
                .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
                .unwrap();

            let idx_var: Vec<AllocatedBit> = large_leaf_idx_in_bits
                .clone()
                .into_iter()
                .enumerate()
                .map(|(i, b)| {
                    AllocatedBit::alloc(cs.namespace(|| format!("{} : idx {}", j, i)), Some(b))
                })
                .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()
                .unwrap();
            let is_valid = Boolean::from(
                path_verify_circuit::<Fp, U1, U1, U2, LEAF_SIZE, HEIGHT, _>(
                    &mut cs.namespace(|| format!("{} : is_valid false", j)),
                    root_var,
                    val_var.clone(),
                    idx_var.clone(),
                    siblings_var,
                )
                .unwrap(),
            );
            Boolean::enforce_equal(
                &mut cs.namespace(|| format!("{} : enforce true", j)),
                &is_valid,
                &Boolean::constant(true),
            )
            .unwrap();
        }

        assert!(cs.is_satisfied());
    }
}
