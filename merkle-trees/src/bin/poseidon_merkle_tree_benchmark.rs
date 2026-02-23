//! Simple example demonstrating building a BabyBear Merkle tree with Poseidon2 hash
//! Based on https://github.com/Plonky3/Plonky3/blob/main/merkle-tree/benches/merkle_tree.rs

use p3_baby_bear::{BabyBear, default_babybear_poseidon2_16};
use p3_commit::Mmcs;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use std::time::Instant;

// Type alias for the field
type F = BabyBear;

// Poseidon2 width
const WIDTH: usize = 16;

// Sponge parameters: RATE is how many field elements absorbed per permutation
const RATE: usize = 8;

// Output size (number of field elements in digest)
const OUT: usize = 8;

fn main() {
    println!("BabyBear Merkle Tree with Poseidon2 Hash Example");
    println!("=================================================\n");

    // Create the Poseidon2 permutation with default round constants
    let poseidon2 = default_babybear_poseidon2_16();

    // Wrap the permutation in a padding-free sponge for hashing
    // PaddingFreeSponge<Perm, WIDTH, RATE, OUT>
    let hasher = PaddingFreeSponge::<_, WIDTH, RATE, OUT>::new(poseidon2.clone());

    // Create a compression function for the Merkle tree internal nodes
    // TruncatedPermutation<Perm, N, CHUNK, WIDTH> where:
    // - N: number of chunks to absorb (2 for binary tree)
    // - CHUNK: size of each chunk (should match OUT)
    // - WIDTH: permutation width
    let compressor = TruncatedPermutation::<_, 2, OUT, WIDTH>::new(poseidon2);

    // Create the Merkle tree MMCS (Mixed Matrix Commitment Scheme)
    // MerkleTreeMmcs<P, PW, H, C, DIGEST_ELEMS>
    // P = field element type, PW = packed width type (same as P for no packing)
    let mmcs = MerkleTreeMmcs::<F, F, _, _, OUT>::new(hasher, compressor);

    // Generate some example data: a matrix of random field elements
    // Rows represent leaves, columns represent data per leaf
    let num_rows = 1 << 25; // 1024 leaves
    let num_cols = 8;      // 8 field elements per leaf

    println!("Generating matrix: {} rows × {} cols", num_rows, num_cols);

    // Create deterministic data using BabyBear::new()
    let data: Vec<F> = (0..num_rows * num_cols)
        .map(|i| BabyBear::new(((i * 7 + 13) % (1 << 27)) as u32))
        .collect();

    let matrix = RowMajorMatrix::new(data, num_cols);

    // Commit to the matrix (builds the Merkle tree)
    println!("\nBuilding Merkle tree...");
    let start = Instant::now();
    let (commitment, prover_data) = mmcs.commit(vec![matrix.clone()]);
    let commit_time = start.elapsed();

    println!("Commitment time: {:?}", commit_time);
    println!("Root hash: {:?}", commitment);

    // Open a proof for a specific row
    let row_to_open = 42;
    println!("\nOpening proof for row {}...", row_to_open);

    let start = Instant::now();
    let batch_opening = mmcs.open_batch(row_to_open, &prover_data);
    let open_time = start.elapsed();

    println!("Open time: {:?}", open_time);
    println!("Opened values (first 4 of first matrix): {:?}", &batch_opening.opened_values[0][..4]);

    // Verify the proof
    println!("\nVerifying proof...");
    let start = Instant::now();

    // Get dimensions for verification
    let dimensions = vec![matrix.dimensions()];

    let verification_result = mmcs.verify_batch(
        &commitment,
        &dimensions,
        row_to_open,
        (&batch_opening).into(),
    );
    let verify_time = start.elapsed();

    match verification_result {
        Ok(()) => println!("✓ Proof verified successfully in {:?}", verify_time),
        Err(e) => println!("✗ Verification failed: {:?}", e),
    }

    // Summary
    println!("\n=== Summary ===");
    println!("Field: BabyBear (p = 2^31 - 2^27 + 1)");
    println!("Hash: Poseidon2 (width={})", WIDTH);
    println!("Tree size: {} leaves", num_rows);
    println!("Leaf size: {} field elements", num_cols);
    println!("Total commit time: {:?}", commit_time);
    println!("Proof generation: {:?}", open_time);
    println!("Proof verification: {:?}", verify_time);
}
