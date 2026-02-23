use merkle_trees::split_merkle_tree_sha256::tree::{idx_to_bits, Leaf, SplitMerkleTree};
use rand::thread_rng;
use rand::Rng;
use rs_merkle::{algorithms::Sha256, Hasher, MerkleTree};
use std::time::Instant;

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

    // Generate random leaves (32 bytes each, similar to field elements)
    let leaves: Vec<Leaf> = (0..FIELD_ELEMENTS_IN_GENOME)
        .map(|_| {
            let mut val = vec![0u8; 32];
            rng.fill(&mut val[..]);
            Leaf { val }
        })
        .collect();

    const NUM_LEAVES: usize = FIELD_ELEMENTS_IN_GENOME;
    const TOTAL_MERKLE_TREE_HEIGHT: usize = ceil_log2(NUM_LEAVES);

    const TOP_TREE_HEIGHT: usize = 17;
    const BOTTOM_TREE_HEIGHT: usize = TOTAL_MERKLE_TREE_HEIGHT - TOP_TREE_HEIGHT;

    let empty_leaf_val = Leaf::default();
    let build_start = Instant::now();
    let tree: SplitMerkleTree<TOP_TREE_HEIGHT, BOTTOM_TREE_HEIGHT, TOTAL_MERKLE_TREE_HEIGHT> =
        SplitMerkleTree::from_vec(leaves.clone(), empty_leaf_val.clone());
    let build_time = build_start.elapsed();

    const NUM_PROOF_SAMPLES: usize = 100;

    // Generate random indices for benchmarking
    let random_indices: Vec<usize> = (0..NUM_PROOF_SAMPLES)
        .map(|_| rng.gen_range(0..FIELD_ELEMENTS_IN_GENOME))
        .collect();

    // Benchmark split tree proof generation
    let mut split_proof_times = Vec::with_capacity(NUM_PROOF_SAMPLES);
    let mut split_verify_times = Vec::with_capacity(NUM_PROOF_SAMPLES);
    let mut all_valid = true;

    for &idx_raw in &random_indices {
        let idx_bits = idx_to_bits(TOTAL_MERKLE_TREE_HEIGHT, idx_raw);
        let leaf = &leaves[idx_raw];

        let proof_start = Instant::now();
        let proof = tree.get_siblings_path(idx_bits.clone());
        split_proof_times.push(proof_start.elapsed());

        let verify_start = Instant::now();
        let is_valid = tree.verify(idx_bits.clone(), leaf, &proof);
        split_verify_times.push(verify_start.elapsed());
        all_valid &= is_valid;
    }

    let avg_split_proof_time: std::time::Duration =
        split_proof_times.iter().sum::<std::time::Duration>() / NUM_PROOF_SAMPLES as u32;
    let avg_split_verify_time: std::time::Duration =
        split_verify_times.iter().sum::<std::time::Duration>() / NUM_PROOF_SAMPLES as u32;

    println!("=== Split Merkle Tree (SHA256) ===");
    println!(
        "Tree Height:  {:?}, (top section: {:?}, bottom section: {:?})",
        TOTAL_MERKLE_TREE_HEIGHT, TOP_TREE_HEIGHT, BOTTOM_TREE_HEIGHT
    );
    let data_bytes = (FIELD_ELEMENTS_IN_GENOME * 32) as f64;
    let overhead_pct = (tree.additional_storage_used() as f64 / data_bytes) * 100.0;
    println!(
        "Tree additional size: {:?}B (overhead: {:.2}%)",
        tree.additional_storage_used(),
        overhead_pct
    );
    println!("Tree build:   {:?}", build_time);
    println!(
        "Proof gen (avg of {}): {:?}",
        NUM_PROOF_SAMPLES, avg_split_proof_time
    );
    println!(
        "Proof verify (avg of {}): {:?} (all valid = {})",
        NUM_PROOF_SAMPLES, avg_split_verify_time, all_valid
    );

    // ========================================
    // Regular Merkle Tree benchmark
    // ========================================
    println!("\n=== Regular Merkle Tree (SHA256, rs_merkle) ===");

    // Hash all leaves first
    let hash_start = Instant::now();
    let leaf_hashes: Vec<[u8; 32]> = leaves.iter().map(|leaf| Sha256::hash(&leaf.val)).collect();
    let hash_time = hash_start.elapsed();
    println!("Leaf hashing: {:?}", hash_time);

    // Build regular merkle tree
    let regular_build_start = Instant::now();
    let regular_tree = MerkleTree::<Sha256>::from_leaves(&leaf_hashes);
    let regular_build_time = regular_build_start.elapsed();

    let regular_root = regular_tree.root().expect("tree should have root");
    println!("Tree build:   {:?}", regular_build_time);
    println!(
        "Total (hash + build): {:?}",
        hash_time + regular_build_time
    );

    // Benchmark regular tree proof generation using the same random indices
    let mut regular_proof_times = Vec::with_capacity(NUM_PROOF_SAMPLES);
    let mut regular_verify_times = Vec::with_capacity(NUM_PROOF_SAMPLES);
    let mut regular_all_valid = true;

    for &idx_raw in &random_indices {
        let proof_start = Instant::now();
        let proof = regular_tree.proof(&[idx_raw]);
        regular_proof_times.push(proof_start.elapsed());

        let verify_start = Instant::now();
        let is_valid = proof.verify(
            regular_root,
            &[idx_raw],
            &[leaf_hashes[idx_raw]],
            leaf_hashes.len(),
        );
        regular_verify_times.push(verify_start.elapsed());
        regular_all_valid &= is_valid;
    }

    let avg_regular_proof_time: std::time::Duration =
        regular_proof_times.iter().sum::<std::time::Duration>() / NUM_PROOF_SAMPLES as u32;
    let avg_regular_verify_time: std::time::Duration =
        regular_verify_times.iter().sum::<std::time::Duration>() / NUM_PROOF_SAMPLES as u32;

    println!(
        "Proof gen (avg of {}): {:?}",
        NUM_PROOF_SAMPLES, avg_regular_proof_time
    );
    println!(
        "Proof verify (avg of {}): {:?} (all valid = {})",
        NUM_PROOF_SAMPLES, avg_regular_verify_time, regular_all_valid
    );

    // Summary comparison
    println!("\n=== Comparison ===");
    println!(
        "Proof gen speedup (regular vs split): {:.2}x",
        avg_split_proof_time.as_secs_f64() / avg_regular_proof_time.as_secs_f64()
    );
}
