use ark_bn254::{Bn254, Fr};
use ark_ff::{BigInteger, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, Polynomial};
use ark_poly_commit::kzg10::{KZG10, Powers, VerifierKey};
use std::borrow::Cow;
use ark_std::test_rng;
use std::time::Instant;
use clap::Parser;
use serde::Deserialize;

#[derive(Parser)]
struct Args {
    prover_toml_path: std::path::PathBuf,
}

#[derive(Deserialize, Debug)]
struct ProverToml {
    #[serde(rename = "X")]
    x: Vec<Vec<String>>,
    y: Vec<String>,
    beta: Vec<String>,
    regularization_constraint: String,
    challenge: String,
}

fn main() {
    let args = Args::parse();
    let contents = std::fs::read_to_string(&args.prover_toml_path).expect("Failed to read file");
    let parsed: ProverToml = toml::from_str(&contents).expect("Failed to parse toml");

    let x: Vec<Vec<u128>> = parsed.x.iter()
        .map(|row| row.iter().map(|s| s.parse::<u128>().expect("Parsing field element failed")).collect())
        .collect();

    let y: Vec<u128> = parsed.y.iter()
        .map(|s| s.parse::<u128>().expect("Parsing field element failed"))
        .collect();

    let x_felts: Vec<Vec<Fr>> = x.iter()
        .map(|row| row.iter().map(|&v| Fr::from(v)).collect())
        .collect();

    let y_felts: Vec<Fr> = y.iter().map(|&v| Fr::from(v)).collect();

    let challenge: Fr = parsed.challenge.parse().expect("Invalid Fr for challenge");

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
    println!("auth_hash: 0x{}", bytes.iter().map(|b| format!("{:02x}", b)).collect::<String>());

    // Build polynomial for commuitment.
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
    assert_eq!(poly.evaluate(&challenge), auth_hash, "polynomial evaluation mismatch");

    let rng = &mut test_rng();

    let start = Instant::now();
    let pp = KZG10::<Bn254, DensePolynomial<Fr>>::setup(degree, false, rng)
        .expect("PCS setup failed");
    println!("Setup took {:?}", start.elapsed());

    // Emulating the trim() function here: 
    // https://github.com/arkworks-rs/poly-commit/blob/a05ec99d0d3e46c8ba0d6d3592980777bc2847e8/poly-commit/src/kzg10/mod.rs#L491
    let powers = Powers {
        powers_of_g: Cow::Borrowed(&pp.powers_of_g[..=degree]),
        powers_of_gamma_g: Cow::Owned(
            (0..=degree).map(|i| pp.powers_of_gamma_g[&i]).collect()
        ),
    };
    let vk = VerifierKey {
        g: pp.powers_of_g[0],
        gamma_g: pp.powers_of_gamma_g[&0],
        h: pp.h,
        beta_h: pp.beta_h,
        prepared_h: pp.prepared_h.clone(),
        prepared_beta_h: pp.prepared_beta_h.clone(),
    };

    let start = Instant::now();
    let (commitment, randomness) = KZG10::<Bn254, DensePolynomial<Fr>>::commit(&powers, &poly, None, None)
        .expect("PCS commit failed");
    println!("Commitment took {:?}", start.elapsed());

    let start = Instant::now();
    let proof = KZG10::<Bn254, DensePolynomial<Fr>>::open(&powers, &poly, challenge, &randomness)
        .expect("PCS open failed");
    println!("Opening took {:?}", start.elapsed());

    let start = Instant::now();
    let valid = KZG10::<Bn254, DensePolynomial<Fr>>::check(&vk, &commitment, challenge, auth_hash, &proof)
        .expect("PCS check failed");
    println!("Veriication took {:?}", start.elapsed());

    assert!(valid, "PCS proof verification failed");

    println!("PCS commitment: {:?}", commitment);
    println!("PCS proof verified successfully");
}
