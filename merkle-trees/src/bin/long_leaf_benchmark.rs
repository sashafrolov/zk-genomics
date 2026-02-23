use generic_array::typenum::{U1, U2};
use ff::Field;
use merkle_trees::large_leaf_merkle_tree::tree::LargeLeafMerkleTree;
use merkle_trees::vanilla_tree::tree::{idx_to_bits, Leaf};
use spartan2::provider::T256HyraxEngine;
use spartan2::traits::Engine;
use rand::thread_rng;
use rand::Rng;
use std::time::Instant;

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
    let leaves: Vec<<E as Engine>::Scalar> = (0..FIELD_ELEMENTS_IN_GENOME)
        .map(|_| <E as Engine>::Scalar::random(&mut rng))
        .collect();

    // let log_leaf_sizes: Vec<usize> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    const LEAF_SIZE: usize = 1 << 1;

    const NUM_LEAVES: usize = (FIELD_ELEMENTS_IN_GENOME + LEAF_SIZE - 1) / LEAF_SIZE;
    const HEIGHT: usize = ceil_log2(NUM_LEAVES);

    let empty_leaf_val = Leaf::default();
    let build_start = Instant::now();
    let tree: LargeLeafMerkleTree<<E as Engine>::Scalar, LEAF_SIZE, HEIGHT, U1, U1, U2> =
        LargeLeafMerkleTree::from_vec(leaves.clone(), empty_leaf_val.clone());
    let build_time = build_start.elapsed();

    const NUM_PROOF_SAMPLES: usize = 100;
    let idx_bits_len: usize = ((LEAF_SIZE * (1 << HEIGHT)) as f64).log2().ceil() as usize;

    // Generate 100 random indices and measure proof generation time for each
    let mut total_proof_time = std::time::Duration::ZERO;
    let mut last_proof = None;
    let mut last_idx_bits = None;
    let mut last_leaf = None;

    for _ in 0..NUM_PROOF_SAMPLES {
        let idx_raw: u64 = rng.gen_range(0..FIELD_ELEMENTS_IN_GENOME as u64);
        let idx_bits = idx_to_bits(idx_bits_len, <E as Engine>::Scalar::from(idx_raw));
        let leaf = leaves[idx_raw as usize];

        let proof_start = Instant::now();
        let proof = tree.get_siblings_path(idx_bits.clone());
        total_proof_time += proof_start.elapsed();

        last_proof = Some(proof);
        last_idx_bits = Some(idx_bits);
        last_leaf = Some(leaf);
    }

    let avg_proof_time = total_proof_time / NUM_PROOF_SAMPLES as u32;

    // Verify the last proof to ensure correctness
    let verify_start = Instant::now();
    let is_valid = tree.verify(last_idx_bits.clone().unwrap(), last_leaf.unwrap(), &last_proof.unwrap());
    let verify_time = verify_start.elapsed();

    println!("Tree height:  {:?}, (leaf size: {:?})", HEIGHT, LEAF_SIZE);
    println!("Tree additional size: {:?}B", tree.additional_storage_used());
    println!("Tree build:   {:?}", build_time);
    println!("Proof gen:    {:?} (avg over {} samples)", avg_proof_time, NUM_PROOF_SAMPLES);
    println!("Proof verify: {:?} (valid = {})", verify_time, is_valid);
}
