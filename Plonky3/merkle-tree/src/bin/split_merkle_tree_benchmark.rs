//! Based on https://github.com/Plonky3/Plonky3/blob/main/merkle-tree/benches/merkle_tree.rs

use p3_baby_bear::{BabyBear, default_babybear_poseidon2_16};
use p3_commit::Mmcs;
use p3_field::PrimeField32;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::{RngExt, SeedableRng};
use rand::rngs::SmallRng;
use std::fs::{self, File};
use std::io::{BufReader, BufWriter, Read as _, Seek, SeekFrom, Write};
use std::path::Path;
use std::time::{Duration, Instant};

type F = BabyBear;

// Default parameters, 8 Babybear field elements is about 256 bits
const WIDTH: usize = 16;
const RATE: usize = 8;
const OUT: usize = 8;

fn main() {
    let tmp_dir = Path::new("tmp");
    fs::create_dir_all(tmp_dir).expect("failed to create tmp directory");

    println!("Split Merkle Tree benchmark");
    println!("=================================================\n");

    // Default Plonky3 parameters
    let poseidon2 = default_babybear_poseidon2_16();

    let hasher = PaddingFreeSponge::<_, WIDTH, RATE, OUT>::new(poseidon2.clone());

    // https://eprint.iacr.org/2026/089 hehehe
    let compressor = TruncatedPermutation::<_, 2, OUT, WIDTH>::new(poseidon2);

    let mmcs = MerkleTreeMmcs::<F, F, _, _, OUT>::new(hasher, compressor);

    // Rows represent leaves, columns represent data per leaf (because of MMCS formalism)
    const LOG_MAX_HEIGHT : usize = 25;
    let num_rows = 1 << LOG_MAX_HEIGHT; 
    let num_cols = 8; // 8 field elements per leaf, optimally uses a hash.

    println!("Generating matrix: {} rows × {} cols", num_rows, num_cols);
    let mut rng = SmallRng::seed_from_u64(676767);
    let matrix = RowMajorMatrix::<F>::rand(&mut rng, num_rows, num_cols);

    println!("Building Merkle tree...");
    let start = Instant::now();
    let (commitment, prover_data) = mmcs.commit(vec![matrix.clone()]);
    let commit_time = start.elapsed();

    println!("Merkle Tree build time: {:?}", commit_time);
    // println!("Root hash: {:?}", commitment);
    
    // Write the layers of the Merkle Tree to FS.
    let digest_layers = prover_data.digest_layers();
    println!("=== Writing out Digest Layers ===");
    let start = Instant::now();
    for (i, layer) in digest_layers.iter().enumerate() {
        let path = tmp_dir.join(format!("layer_{}_hashes", i));
        let mut writer = BufWriter::new(File::create(&path).expect("failed to create layer file"));
        for digest in layer {
            for elem in digest {
                writer
                    .write_all(&elem.as_canonical_u32().to_le_bytes())
                    .expect("failed to write digest");
            }
        }
        writer.flush().expect("failed to flush layer file");
        println!("  Wrote layer {}: {} digests to {}", i, layer.len(), path.display());
    }
    let write_time = start.elapsed();
    println!("Digest layers write time: {:?}", write_time);


    let h_splits = vec![3, 4, 5, 6, 7, 8, 9, 10, 15, 20];
    const NUM_PROVE_RUNS: usize = 100;

    let digest_bytes = OUT * 4;
    let vanilla_total_bytes: u64 = digest_layers.iter().map(|l| l.len() as u64 * digest_bytes as u64).sum();
    println!("\n=== Benchmarking Vanilla Merkle Tree ===");
    println!("Vanilla tree: storing {} layers ({} bytes / {} MB)", LOG_MAX_HEIGHT, vanilla_total_bytes, vanilla_total_bytes / (1024 * 1024));
    let mut total_open_time = Duration::ZERO;
    let mut total_verify_time = Duration::ZERO;
    for _ in 0..NUM_PROVE_RUNS {
        let row_to_open = rng.random_range(0..num_rows);

        let start = Instant::now();

        // Read the opened row directly from the matrix
        let opened_values: Vec<Vec<F>> = vec![matrix.row(row_to_open).unwrap().into_iter().collect()];

        // Read sibling digests from layer files on disk
        let digest_bytes = OUT * 4; // 8 elements × 4 bytes each = 32 bytes per digest
        let mut proof: Vec<[F; OUT]> = Vec::with_capacity(LOG_MAX_HEIGHT);
        for i in 0..LOG_MAX_HEIGHT {
            let sibling_index = (row_to_open >> i) ^ 1;
            let path = tmp_dir.join(format!("layer_{}_hashes", i));
            let mut file = BufReader::new(File::open(&path).expect("failed to open layer file"));
            file.seek(SeekFrom::Start((sibling_index * digest_bytes) as u64))
                .expect("failed to seek");
            let mut buf = [0u8; 4];
            let mut digest = [BabyBear::new(0); OUT];
            for elem in &mut digest {
                file.read_exact(&mut buf).expect("failed to read digest element");
                *elem = BabyBear::new(u32::from_le_bytes(buf));
            }
            proof.push(digest);
        }

        let batch_opening = p3_commit::BatchOpening::new(opened_values, proof);
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
    println!("Average open time (from disk) for vanilla tree: {:?}", total_open_time / NUM_PROVE_RUNS as u32);
    println!("Average verify time for vanilla tree: {:?}", total_verify_time / NUM_PROVE_RUNS as u32);

    for &h_split in &h_splits {
        println!("\n=== Benchmarking Split Merkle Tree with h_split = {} ===", h_split);
        let chunk_size = 1usize << h_split;
        let digest_bytes = OUT * 4;
        let mut total_bytes: u64 = 0;
        for i in h_split..LOG_MAX_HEIGHT {
            let layer_digests = digest_layers[i].len() as u64;
            total_bytes += layer_digests * digest_bytes as u64;
        }
        println!("h_split {}: storing {} layers ({} bytes / {} KB)", h_split, LOG_MAX_HEIGHT - h_split, total_bytes, total_bytes / 1024);

        let mut total_open_time = Duration::ZERO;
        let mut total_verify_time = Duration::ZERO;
        // Generate inclusion proofs from disk a bunch of times.
        for _ in 0..NUM_PROVE_RUNS {
            let row_to_open = rng.random_range(0..num_rows);
            let chunk_start_index = (row_to_open / chunk_size) * chunk_size;
            let data_start = chunk_start_index * num_cols;
            let data_end = data_start + chunk_size * num_cols;
            let chunk = RowMajorMatrix::new(matrix.values[data_start..data_end].to_vec(), num_cols);

            let start = Instant::now();
            
            // Read the opened row directly from the matrix
            let opened_values: Vec<Vec<F>> = vec![matrix.row(row_to_open).unwrap().into_iter().collect()];
            // Rebuild subtree
            let (_chunk_commitment, chunk_prover_data) = mmcs.commit(vec![chunk]);

            // Generate inclusion proof within the chunk sub-tree
            let index_in_chunk = row_to_open - chunk_start_index;
            let chunk_opening = mmcs.open_batch(index_in_chunk, &chunk_prover_data);

            // First h_split entries come from the chunk proof, rest from disk
            let mut proof: Vec<[F; OUT]> = Vec::with_capacity(LOG_MAX_HEIGHT);
            proof.extend_from_slice(&chunk_opening.opening_proof);

            // Read remaining sibling digests from layer files on disk
            let digest_bytes = OUT * 4;
            for i in h_split..LOG_MAX_HEIGHT {
                let sibling_index = (row_to_open >> i) ^ 1;
                let path = tmp_dir.join(format!("layer_{}_hashes", i));
                let mut file = BufReader::new(File::open(&path).expect("failed to open layer file"));
                file.seek(SeekFrom::Start((sibling_index * digest_bytes) as u64))
                    .expect("failed to seek");
                let mut buf = [0u8; 4];
                let mut digest = [BabyBear::new(0); OUT];
                for elem in &mut digest {
                    file.read_exact(&mut buf).expect("failed to read digest element");
                    *elem = BabyBear::new(u32::from_le_bytes(buf));
                }
                proof.push(digest);
            }

            let batch_opening = p3_commit::BatchOpening::new(opened_values, proof);
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
        println!("Average open time (from disk) for h_split {}: {:?}", h_split, total_open_time / NUM_PROVE_RUNS as u32);
        println!("Average verify time for h_split {}: {:?}", h_split, total_verify_time / NUM_PROVE_RUNS as u32);
    }

    // Summary
    println!("=== Summary ===");
    println!("Tree size: {} leaves", num_rows);
    println!("Leaf size: {} field elements", num_cols);
    println!("Total commit time: {:?}", commit_time);
    println!("Digest layers write: {:?}", write_time);

    // Clean up tmp directory
    fs::remove_dir_all(tmp_dir).expect("failed to clean up tmp directory");
}
