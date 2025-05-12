// Gives a performance example for Merkle Tree-based succincct data structure with big leaves (section 4.2 in the report).

use itertools::Itertools;
use p3_baby_bear::{BabyBear, DiffusionMatrixBabyBear};
use p3_commit::Mmcs;
use p3_field::{AbstractField, Field};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::{Dimensions, Matrix};
use p3_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::{
    CryptographicHasher, PaddingFreeSponge, PseudoCompressionFunction, TruncatedPermutation,
};
use rand::thread_rng;

use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use std::time::Duration;
use std::time::Instant;

use p3_merkle_tree::FieldMerkleTreeMmcs;

type F = BabyBear;

type Perm = Poseidon2<F, Poseidon2ExternalMatrixGeneral, DiffusionMatrixBabyBear, 16, 7>;
type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type MyMmcs =
    FieldMerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing, MyHash, MyCompress, 8>;

fn seeded_rng() -> impl Rng {
    ChaCha20Rng::seed_from_u64(18)
}

fn main() {
    // Setup the PCS with basic parameters
    let mut rng = seeded_rng();
    let perm = Perm::new_from_rng_128(
        Poseidon2ExternalMatrixGeneral,
        DiffusionMatrixBabyBear::default(),
        &mut rng,
    );
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm);
    let mmcs = MyMmcs::new(hash, compress);

    // Large enough to fit human genome in the blocks.
    static NUM_BLOCKS: usize = 200_000_000usize.next_power_of_two();
    static LEAF_SIZE: usize = 1 << 7; // log log n is a bit less than 5
    static NUM_LEAVES: usize = NUM_BLOCKS / LEAF_SIZE;
    static INDEX_FOR_MEMBERSHIP_PROOF: usize = 1;

    let data: Vec<u8> = (0..NUM_BLOCKS).map(|_| rng.next_u32() as u8).collect();
    // let image_copy = image.clone();
    let mut data_as_felts: Vec<BabyBear> = data
        .into_iter()
        .map(|chunk| BabyBear::new((chunk as u32)))
        .collect();

    let data_matrix = RowMajorMatrix::new(data_as_felts, LEAF_SIZE);

    let commit_start = Instant::now();
    let (commit, prover_data) = mmcs.commit(vec![data_matrix]);
    let commit_duration = commit_start.elapsed();
    println!("Building merkle tree took: {:?}", commit_duration);

    let prover_data_string = format!("{:?}", prover_data);
    let start_marker = "digest_layers: [[[";
    let end_marker = "]]]";
    
    let start = prover_data_string.find(start_marker).unwrap() + start_marker.len();
    let end = prover_data_string[start..].find(end_marker).unwrap() + start;

    let merkle_tree_string = &prover_data_string[start..end]; 

    // hacky way to get number of hashes in merkle tree since this library is not great about exposing everything i want.
    let hashes_in_merkle_tree = merkle_tree_string.matches(", [").count() + 1;

    println!("This many hashes in Merkle Tree {}", hashes_in_merkle_tree);
    let bytes_in_merkle_tree = hashes_in_merkle_tree * 32; // bytes assuming a BabyBear field element takes up 32 bytes
    println!("This many bytes in Merkle Tree {}", bytes_in_merkle_tree);

    let proof_generation_start = Instant::now();
    let proof = mmcs.open_batch(INDEX_FOR_MEMBERSHIP_PROOF, &prover_data);

    let proof_duration = proof_generation_start.elapsed();
    println!("Proof generation took: {:?}", proof_duration);

    let video_matrix_dims = vec![Dimensions {
        height: NUM_LEAVES,
        width: LEAF_SIZE,
    }];

    let proof_verification_start = Instant::now();
    let (opened_values, proof) = proof;
    mmcs.verify_batch(
        &commit,
        &video_matrix_dims,
        INDEX_FOR_MEMBERSHIP_PROOF,
        &opened_values,
        &proof,
    )
    .expect("expected verification to succeed");

    let verification_duration = proof_verification_start.elapsed();
    println!("Proof verification took: {:?}", verification_duration);
}
