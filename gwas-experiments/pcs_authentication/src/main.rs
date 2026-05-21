use ark_bn254::{Bn254, Fr};
use ark_ff::{BigInteger, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, Polynomial};
use ark_poly_commit::kzg10::{KZG10, Powers, VerifierKey};
use ark_std::test_rng;
use clap::Parser;
use serde::Deserialize;
use std::borrow::Cow;
use std::str::FromStr;
use std::time::{Duration, Instant};

#[derive(Parser)]
struct Args {
    prover_toml_path: std::path::PathBuf,
}

#[derive(Deserialize, Debug)]
struct ProverToml {
    #[serde(rename = "X")]
    x: Vec<Vec<String>>,
    y: Vec<String>,
    // We ignore beta and regularization_constraint since PCS only authenticates X and Y
}

// Helper to safely parse large integer strings directly into field elements
fn parse_fr(val_str: &str) -> Fr {
    Fr::from_str(val_str).unwrap_or_else(|_| panic!("Failed to parse string into Fr: {}", val_str))
}

fn main() {
    let args = Args::parse();
    let contents = std::fs::read_to_string(&args.prover_toml_path).expect("Failed to read file");

    // We parse only what we need for PCS.
    let toml_val: toml::Value = toml::from_str(&contents).expect("Failed to parse TOML");

    let challenge_str = toml_val
        .get("challenge")
        .expect("Missing challenge")
        .as_str()
        .expect("Challenge is not a string");
    let challenge = parse_fr(challenge_str);

    let x_felts: Vec<Vec<Fr>> = toml_val
        .get("X")
        .expect("Missing X")
        .as_array()
        .expect("X is not an array")
        .iter()
        .map(|row| {
            row.as_array()
                .expect("X row is not an array")
                .iter()
                .map(|val| parse_fr(val.as_str().expect("X value is not a string")))
                .collect()
        })
        .collect();

    let y_felts: Vec<Fr> = toml_val
        .get("y")
        .expect("Missing y")
        .as_array()
        .expect("y is not an array")
        .iter()
        .map(|val| parse_fr(val.as_str().expect("y value is not a string")))
        .collect();

    let mut auth_hash = Fr::from(0u64);
    for row in &x_felts {
        for &val in row {
            auth_hash = auth_hash * challenge + val;
        }
    }
    for &val in &y_felts {
        auth_hash = auth_hash * challenge + val;
    }

    let bytes = auth_hash.into_bigint().to_bytes_be();
    println!(
        "auth_hash: 0x{}",
        bytes
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect::<String>()
    );

    // Build polynomial for commitment.
    let mut coeffs: Vec<Fr> = Vec::new();
    for row in &x_felts {
        for &val in row {
            coeffs.push(val);
        }
    }
    for &val in &y_felts {
        coeffs.push(val);
    }

    // DensePolynomial stores coefficients from degree 0 upward, need to reverse.
    coeffs.reverse();
    let poly = DensePolynomial::from_coefficients_vec(coeffs);
    let degree = poly.degree();

    // Sanity check: polynomial should evaluate to auth_hash at challenge
    assert_eq!(
        poly.evaluate(&challenge),
        auth_hash,
        "polynomial evaluation mismatch"
    );

    let rng = &mut test_rng();

    let start = Instant::now();
    let pp =
        KZG10::<Bn254, DensePolynomial<Fr>>::setup(degree, false, rng).expect("PCS setup failed");
    println!("Setup took {:?}", start.elapsed());

    // Emulating the trim() function here:
    let powers = Powers {
        powers_of_g: Cow::Borrowed(&pp.powers_of_g[..=degree]),
        powers_of_gamma_g: Cow::Owned((0..=degree).map(|i| pp.powers_of_gamma_g[&i]).collect()),
    };
    let vk = VerifierKey {
        g: pp.powers_of_g[0],
        gamma_g: pp.powers_of_gamma_g[&0],
        h: pp.h,
        beta_h: pp.beta_h,
        prepared_h: pp.prepared_h.clone(),
        prepared_beta_h: pp.prepared_beta_h.clone(),
    };

    // Number of times to run the benchmarks
    let num_runs: u32 = 100;
    println!(
        "Running benchmarks {} times to calculate average...",
        num_runs
    );

    // --- Benchmark Commitment ---
    let mut total_commit_time = Duration::ZERO;
    let mut final_commitment = None;
    let mut final_randomness = None;

    for _ in 0..num_runs {
        let start = Instant::now();
        let (commitment, randomness) =
            KZG10::<Bn254, DensePolynomial<Fr>>::commit(&powers, &poly, None, None)
                .expect("PCS commit failed");
        total_commit_time += start.elapsed();

        final_commitment = Some(commitment);
        final_randomness = Some(randomness);
    }
    let commitment = final_commitment.unwrap();
    let randomness = final_randomness.unwrap();
    println!("Average Commitment took {:?}", total_commit_time / num_runs);

    // --- Benchmark Opening ---
    let mut total_open_time = Duration::ZERO;
    let mut final_proof = None;

    for _ in 0..num_runs {
        let start = Instant::now();
        let proof =
            KZG10::<Bn254, DensePolynomial<Fr>>::open(&powers, &poly, challenge, &randomness)
                .expect("PCS open failed");
        total_open_time += start.elapsed();

        final_proof = Some(proof);
    }
    let proof = final_proof.unwrap();
    println!("Average Opening took {:?}", total_open_time / num_runs);

    // --- Benchmark Verification ---
    let mut total_verify_time = Duration::ZERO;
    let mut is_valid = false;

    for _ in 0..num_runs {
        let start = Instant::now();
        let valid = KZG10::<Bn254, DensePolynomial<Fr>>::check(
            &vk,
            &commitment,
            challenge,
            auth_hash,
            &proof,
        )
        .expect("PCS check failed");
        total_verify_time += start.elapsed();

        is_valid = valid;
    }
    println!(
        "Average Verification took {:?}",
        total_verify_time / num_runs
    );

    assert!(is_valid, "PCS proof verification failed");

    println!("PCS commitment: {:?}", commitment);
    println!("PCS proof verified successfully");
}
