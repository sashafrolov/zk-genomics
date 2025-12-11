use generic_array::typenum::{U1, U2};
use ff::Field;
use merkle_trees::split_merkle_tree::tree::SplitMerkleTree;
use merkle_trees::vanilla_tree::tree::{idx_to_bits, Leaf};
use spartan2::provider::T256HyraxEngine;
use spartan2::traits::Engine;
use rand::thread_rng;
use rand::Rng;
use std::time::Instant;
use std::marker::PhantomData;

type E = T256HyraxEngine;

// Have to do this evil awful garbage to call log2 in a const function.
const fn ceil_log2(mut n: usize) -> usize {
    if n <= 1 {
        return 0;
    }
    n -= 1;
    let mut pow = 0usize;
    while n > 0 {
        n >>= 1;
        pow += 1;
    }
    pow
}

fn main() {
    const BASE_PAIRS_IN_HUMAN_GENOME: usize = 3_200_000_000; // Haploid Genome, seems to be more common.
    const BASE_PAIRS_PER_FIELD_ELEMENT: usize = 126; // Ed25519 field element can fit ~126 2-bit values.
    const FIELD_ELEMENTS_IN_GENOME: usize =
        (BASE_PAIRS_IN_HUMAN_GENOME + BASE_PAIRS_PER_FIELD_ELEMENT - 1)
            / BASE_PAIRS_PER_FIELD_ELEMENT;

    let mut rng = thread_rng();

    // TODO: Fill this in with actual data.
    let leaves: Vec<Leaf<<E as Engine>::Scalar, U1>> = (0..FIELD_ELEMENTS_IN_GENOME)
        .map(|_| Leaf {
            val: vec![<E as Engine>::Scalar::random(&mut rng)],
            _arity: PhantomData,
        })
        .collect();


    const NUM_LEAVES: usize = FIELD_ELEMENTS_IN_GENOME;
    const TOTAL_MERKLE_TREE_HEIGHT: usize = ceil_log2(NUM_LEAVES);

    const TOP_TREE_HEIGHT: usize = 18;
    const BOTTOM_TREE_HEIGHT: usize = TOTAL_MERKLE_TREE_HEIGHT - TOP_TREE_HEIGHT;

    let empty_leaf_val = Leaf::default();
    let build_start = Instant::now();
    let tree: SplitMerkleTree<<E as Engine>::Scalar, TOP_TREE_HEIGHT, BOTTOM_TREE_HEIGHT, TOTAL_MERKLE_TREE_HEIGHT, U1,  U2> =
        SplitMerkleTree::from_vec(leaves.clone(), empty_leaf_val.clone());
    let build_time = build_start.elapsed();

    let idx_raw: u64 = rng.gen_range(0..FIELD_ELEMENTS_IN_GENOME as u64);
    let idx_bits = idx_to_bits(TOTAL_MERKLE_TREE_HEIGHT, <E as Engine>::Scalar::from(idx_raw));
    let leaf = leaves[idx_raw as usize].clone();

    let proof_start = Instant::now();
    let proof = tree.get_siblings_path(idx_bits.clone());
    let proof_time = proof_start.elapsed();

    let verify_start = Instant::now();
    let is_valid = tree.verify(idx_bits.clone(), &leaf, &proof);
    let verify_time = verify_start.elapsed();

    println!("Tree Height:  {:?}, (top section: {:?}, bottom section: {:?})", TOTAL_MERKLE_TREE_HEIGHT, TOP_TREE_HEIGHT, BOTTOM_TREE_HEIGHT);
    let data_bytes = (FIELD_ELEMENTS_IN_GENOME * 32) as f64;
    let overhead_pct =
        (tree.additional_storage_used() as f64 / data_bytes) * 100.0;
    println!("Tree additional size: {:?}B (overhead: {:.2}%)", tree.additional_storage_used(), overhead_pct);
    println!("Tree build:   {:?}", build_time);
    println!("Proof gen:    {:?}", proof_time);
    println!("Proof verify: {:?} (valid = {})", verify_time, is_valid);
}
