//! Based on https://github.com/Plonky3/Plonky3/blob/main/merkle-tree/benches/merkle_tree.rs

use p3_baby_bear::{BabyBear, default_babybear_poseidon2_16};
use p3_commit::Mmcs;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::{RngExt, SeedableRng};
use rand::rngs::SmallRng;
use std::time::{Duration, Instant};

type F = BabyBear;

// Default parameters, 8 Babybear field elements is about 256 bits
const WIDTH: usize = 16;
const RATE: usize = 8;
const OUT: usize = 8;

fn main() {
    println!("Large Leaf Merkle Tree benchmark");
    println!("=================================================\n");

    // Default Plonky3 parameters
    let poseidon2 = default_babybear_poseidon2_16();

    let hasher = PaddingFreeSponge::<_, WIDTH, RATE, OUT>::new(poseidon2.clone());

    // https://eprint.iacr.org/2026/089 hehehe
    let compressor = TruncatedPermutation::<_, 2, OUT, WIDTH>::new(poseidon2);

    let mmcs = MerkleTreeMmcs::<F, F, _, _, OUT>::new(hasher, compressor);

    // Rows represent leaves, columns represent data per leaf (because of MMCS formalism)
    // The log base 2 of the number of blocks of base pairs in a single leaf.
    let log_leaf_sizes = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    const LOG_MAX_HEIGHT : usize = 25;

    const BASES_PER_BB_FELT: usize = 15;
    const BASES_PER_LEAF: usize = BASES_PER_BB_FELT * OUT;

    for log_leaf_size in log_leaf_sizes {
        println!("\n=== Benchmarking log leaf size {}, bases per leaf {}. ===", log_leaf_size, (1 << log_leaf_size) * BASES_PER_LEAF);
        let log_tree_height = LOG_MAX_HEIGHT - log_leaf_size;
        let num_rows = 1 << log_tree_height; 
        let num_cols = 8 * (1 << log_leaf_size);

        println!("Generating matrix: {} rows × {} cols", num_rows, num_cols);
        let mut rng = SmallRng::seed_from_u64(676767);
        let matrix = RowMajorMatrix::<F>::rand(&mut rng, num_rows, num_cols);

        println!("Building Merkle tree...");
        let start = Instant::now();
        let (commitment, prover_data) = mmcs.commit(vec![matrix.clone()]);
        let commit_time = start.elapsed();

        println!("Merkle Tree build time: {:?}", commit_time);

        const NUM_PROVE_RUNS: usize = 100;

        println!("Benchmarking Large Leaf Merkle Tree, log leaf size {}", log_leaf_size);
        let mut total_open_time = Duration::ZERO;
        let mut total_verify_time = Duration::ZERO;
        for _ in 0..NUM_PROVE_RUNS {
            let row_to_open = rng.random_range(0..num_rows);

            let start = Instant::now();

            let batch_opening = mmcs.open_batch(row_to_open, &prover_data);

            let open_time = start.elapsed();
            total_open_time += open_time;

            // Verify the proof
            let start = Instant::now();
            let dimensions = vec![matrix.dimensions()];

            let verification_result = mmcs.verify_batch(
                &commitment,
                &dimensions,
                row_to_open,
                (&batch_opening).into(),
            );
            let verify_time = start.elapsed();
            verification_result.expect("Verification failed");
            total_verify_time += verify_time;
        }
        println!("Average open time (from memory) for large leaf tree: {:?}", total_open_time / NUM_PROVE_RUNS as u32);
        println!("Average verify time for large leaf tree: {:?}", total_verify_time / NUM_PROVE_RUNS as u32);
    }
}
