use crate::hash::circuit::hash_circuit;
use bellpepper::gadgets::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{PrimeField, PrimeFieldBits};
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::{Arity, Strength};

// M is top merkle tree size, N is bottom merkle tree size. H is the sum
// of M+N, because you can't do math in Rust generics like in C++.
pub fn path_computed_root<
    F: PrimeField + PrimeFieldBits,
    AL: Arity<F>,
    AN: Arity<F>,
    const M: usize,
    const N: usize,
    const H: usize,
    CS: ConstraintSystem<F>,
>(
    cs: &mut CS,
    val_var: Vec<AllocatedNum<F>>,
    mut idx_var: Vec<AllocatedBit>,
    top_siblings_var: Vec<AllocatedNum<F>>,
    bottom_siblings_var: Vec<AllocatedNum<F>>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    assert_eq!(M + N, H);
    assert_eq!(top_siblings_var.len(), M);
    assert_eq!(bottom_siblings_var.len(), N);

    let node_hash_params = Sponge::<F, AN>::api_constants(Strength::Standard);
    let leaf_hash_params = Sponge::<F, AL>::api_constants(Strength::Standard);
    // Hash the leaf.
    let mut cur_hash_var = hash_circuit(
        &mut cs.namespace(|| "hash num -1 :"),
        val_var,
        &leaf_hash_params,
    )
    .unwrap();

    idx_var.reverse(); // Going from leaf to root

    // First verify the bottom subtree path (length N).
    for (i, sibling) in bottom_siblings_var.into_iter().rev().enumerate() {
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

    // Hash bottom root to make it a leaf for the top tree.
    let mut cur_hash_var = hash_circuit(
        &mut cs.namespace(|| "hash num N + 1 :"),
        vec![cur_hash_var],
        &leaf_hash_params,
    )
    .unwrap();

    // Then verify the top segment of the path (length M).
    for (i_raw, sibling) in top_siblings_var.into_iter().rev().enumerate() {
        let i = i_raw + N; // skip the bottom bits already consumed
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
    AN: Arity<F>,
    const M: usize,
    const N: usize,
    const H: usize,
    CS: ConstraintSystem<F>,
>(
    cs: &mut CS,
    root_var: AllocatedNum<F>,
    val_var: Vec<AllocatedNum<F>>,
    mut idx_var: Vec<AllocatedBit>,
    top_siblings_var: Vec<AllocatedNum<F>>,
    bottom_siblings_var: Vec<AllocatedNum<F>>,
) -> Result<AllocatedBit, SynthesisError> {
    assert_eq!(M + N, H);
    assert_eq!(top_siblings_var.len(), M);
    assert_eq!(bottom_siblings_var.len(), N);
    let node_hash_params = Sponge::<F, AN>::api_constants(Strength::Standard);
    let leaf_hash_params = Sponge::<F, AL>::api_constants(Strength::Standard);
    let mut cur_hash_var = hash_circuit(
        &mut cs.namespace(|| "hash num -1 :"),
        val_var,
        &leaf_hash_params,
    )
    .unwrap();

    idx_var.reverse(); // Going from leaf to root

    // First verify the bottom subtree path (length N).
    for (i, sibling) in bottom_siblings_var.into_iter().rev().enumerate() {
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

    // Hash bottom root to make it a leaf for the top tree.
    let mut cur_hash_var = hash_circuit(
        &mut cs.namespace(|| "hash num N + 1 :"),
        vec![cur_hash_var],
        &leaf_hash_params,
    )
    .unwrap();

    // Then verify the top segment of the path (length M).
    for (i_raw, sibling) in top_siblings_var.into_iter().rev().enumerate() {
        let i = i_raw + N; // Adjust i to skip bottom bits already consumed
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
    use crate::split_merkle_tree::tree::SplitMerkleTree;
    use crate::vanilla_tree::tree::{idx_to_bits, Leaf, MerkleTree};
    use bellpepper_core::test_cs::TestConstraintSystem;
    use ff::Field;
    use generic_array::typenum::{U1, U2};
    use pasta_curves::Fp;
    use rand::Rng;
    use std::marker::PhantomData;

    #[test]
    fn test_split_tree_path_verify_circuit() {
        let mut rng = rand::thread_rng();
        const TOTAL_HEIGHT: usize = 12;
        const TOP_HEIGHT: usize = 6;
        const BOTTOM_HEIGHT: usize = 6;
        let leaves_len = 1 << TOTAL_HEIGHT;
        let random_leaves: Vec<Leaf<Fp, U1>> = (0..leaves_len)
            .map(|_| Leaf {
                val: vec![Fp::random(&mut rng)],
                _arity: PhantomData,
            })
            .collect();
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut tree: SplitMerkleTree<Fp, TOP_HEIGHT, BOTTOM_HEIGHT, TOTAL_HEIGHT, U1, U2> =
            SplitMerkleTree::from_vec(random_leaves.clone(), Leaf::default());

        let test_cases: u64 = 10;

        for j in 0..test_cases {
            let idx_raw: u64 = rng.gen_range(0..leaves_len as u64);
            let idx = Fp::from(idx_raw);
            let idx_in_bits = idx_to_bits(TOTAL_HEIGHT, idx);
            let leaf = random_leaves[idx_raw as usize].clone();

            let path = tree.get_siblings_path(idx_in_bits.clone());

            // Allocating all variables
            let root_var: AllocatedNum<Fp> =
                AllocatedNum::alloc_input(cs.namespace(|| format!("root {}", j)), || Ok(tree.root))
                    .unwrap();
            let val_var: Vec<AllocatedNum<Fp>> = leaf
                .clone()
                .val
                .into_iter()
                .enumerate()
                .map(|(i, s)| {
                    AllocatedNum::alloc(cs.namespace(|| format!("{} : leaf vec {}", j, i)), || {
                        Ok(s)
                    })
                })
                .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
                .unwrap();
            let top_siblings_var: Vec<AllocatedNum<Fp>> = path
                .top_path
                .siblings
                .into_iter()
                .enumerate()
                .map(|(i, s)| {
                    AllocatedNum::alloc(
                        cs.namespace(|| format!("{} : top sibling {}", j, i)),
                        || Ok(s),
                    )
                })
                .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
                .unwrap();
            let bottom_siblings_var: Vec<AllocatedNum<Fp>> = path
                .bottom_path
                .siblings
                .into_iter()
                .enumerate()
                .map(|(i, s)| {
                    AllocatedNum::alloc(
                        cs.namespace(|| format!("{} : bottom sibling {}", j, i)),
                        || Ok(s),
                    )
                })
                .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
                .unwrap();
            let idx_var: Vec<AllocatedBit> = idx_in_bits
                .clone()
                .into_iter()
                .enumerate()
                .map(|(i, b)| {
                    AllocatedBit::alloc(cs.namespace(|| format!("{} : idx {}", j, i)), Some(b))
                })
                .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()
                .unwrap();
            let is_valid = Boolean::from(
                path_verify_circuit::<Fp, U1, U2, TOP_HEIGHT, BOTTOM_HEIGHT, TOTAL_HEIGHT, _>(
                    &mut cs.namespace(|| format!("{} : is_valid false", j)),
                    root_var,
                    val_var.clone(),
                    idx_var.clone(),
                    top_siblings_var,
                    bottom_siblings_var,
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
