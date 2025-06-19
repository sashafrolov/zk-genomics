// This file is largely adopted from the VeriTAS paper (thank you Trisha) because it was already doing
// basically what I needed.

use ark_bls12_381::{Bls12_381, Fr};
use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;

use ark_crypto_primitives::sponge::{CryptographicSponge, FieldBasedCryptographicSponge};
use ark_ff::vec::Vec;
use ark_ff::PrimeField;
use ark_ff::UniformRand;
use ark_ff::{BigInt, BigInteger};
use ark_groth16::Groth16;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::bits::ToBitsGadget;
use ark_r1cs_std::ToConstraintFieldGadget;
use ark_r1cs_std::{prelude::*, uint128::UInt128};
use ark_relations::r1cs::ConstraintSystem;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_relations::*;
use ark_std::rand::{RngCore, SeedableRng};
use ark_std::test_rng;
use ark_std::Zero;
use ark_std::time::{SystemTime, UNIX_EPOCH};
use rand::Rng;
use alignment_circuits::poseidon_parameters_for_test;
use ark_relations::r1cs::{ConstraintLayer, TracingMode};
use tracing_subscriber::layer::SubscriberExt;

const BASES_PER_BLOCK: usize = 125;
const SEQUENCE_BLOCK_LENGTH: usize = 1 << 6;
const SEQUENCE_BASE_PAIRS: usize = SEQUENCE_BLOCK_LENGTH * BASES_PER_BLOCK;
const CIGAR_STRING_LENGTH: usize = SEQUENCE_BASE_PAIRS;
const CIGAR_STRING_LENGTH_BLOCKS: usize = SEQUENCE_BASE_PAIRS.div_ceil(BASES_PER_BLOCK);


pub struct AlignmentCircuit<F: PrimeField> {
    pub reference_sequence_felts: Vec<F>, // The reference for a certain gene, encoded as field elements, where 125 bases are packed per field element
    pub reference_sequence_bases: Vec<usize>, // Reference sequence encoded as usize's between 0 and 4
    pub target_sequence_felts: Vec<F>, // The value being aligned against the target
    pub target_sequence_bases: Vec<usize>,
    pub cigar_string_felts: Vec<F>, // Not fully a CIGAR string yet
    pub cigar_string_bases: Vec<usize>, // encoded as usizes between 0 and 3
    pub alignment_score: usize, // claimed alignment score which is a public output. 0 is perfect, +1 for each insertion or deletion in the basic version.
}

#[allow(dead_code)]
impl<F: PrimeField> AlignmentCircuit<F> {
    pub fn new(
        reference_sequence_felts: Vec<F>,
        reference_sequence_bases: Vec<usize>,
        target_sequence_felts: Vec<F>,
        target_sequence_bases: Vec<usize>,
        cigar_string_felts: Vec<F>,
        cigar_string_bases: Vec<usize>,
        alignment_score: usize,
    ) -> Self {
        Self {
            reference_sequence_felts,
            reference_sequence_bases,
            target_sequence_felts,
            target_sequence_bases,
            cigar_string_felts,
            cigar_string_bases,
            alignment_score,
        }
    }
}

impl<F: PrimeField> Clone for AlignmentCircuit<F> {
    fn clone(&self) -> Self {
        AlignmentCircuit {
            reference_sequence_felts: self.reference_sequence_felts.clone(),
            reference_sequence_bases: self.reference_sequence_bases.clone(),
            target_sequence_felts: self.target_sequence_felts.clone(),
            target_sequence_bases: self.target_sequence_bases.clone(),
            cigar_string_felts: self.cigar_string_felts.clone(),
            cigar_string_bases: self.cigar_string_bases.clone(),
            alignment_score: self.alignment_score,
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for AlignmentCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let mut reference_sequence_vars = Vec::new();
        for elem in self.reference_sequence_felts.iter() {
            reference_sequence_vars.push(FpVar::new_witness(cs.clone(), || Ok(elem))?);
        }

        let mut target_sequence_vars = Vec::new();
        for elem in self.target_sequence_felts.iter() {
            target_sequence_vars.push(FpVar::new_witness(cs.clone(), || Ok(elem))?);
        }

        let mut cigar_string_vars = Vec::new();
        for elem in self.cigar_string_felts.iter() {
            cigar_string_vars.push(FpVar::new_witness(cs.clone(), || Ok(elem))?);
        }

        let params = poseidon_parameters_for_test();

        let mut reference_sponge = PoseidonSpongeVar::new(cs.clone(), &params);
        reference_sponge.absorb(&reference_sequence_vars)?;
        let reference_hash = reference_sponge.squeeze_field_elements(1)?;

        let mut target_sponge = PoseidonSpongeVar::new(cs.clone(), &params);
        target_sponge.absorb(&target_sequence_vars)?;
        let target_hash = target_sponge.squeeze_field_elements(1)?;

        let mut cigar_sponge = PoseidonSpongeVar::new(cs.clone(), &params);
        cigar_sponge.absorb(&cigar_string_vars)?;
        let cigar_hash = cigar_sponge.squeeze_field_elements(1)?;

        let vars_for_fs_hash = vec![&reference_hash[0], &target_hash[0], &cigar_hash[0]];
        let mut challenge_sponge = PoseidonSpongeVar::new(cs.clone(), &params);
        challenge_sponge.absorb(&vars_for_fs_hash)?;
        let challenge_vars = challenge_sponge.squeeze_field_elements(2)?;

        let mut reference_bases = Vec::new();
        let two = FpVar::new_constant(cs.clone(), F::one() + F::one()).unwrap();
        for block in reference_sequence_vars {
            let block_bits = &block.to_bits_le().unwrap();
            let mut chunks = block_bits[0..250].chunks_exact(2);
            for bit_pair in chunks.by_ref().take(BASES_PER_BLOCK) {
                let new_bp = &bit_pair[0].to_constraint_field().unwrap()[0] + &two * &bit_pair[1].to_constraint_field().unwrap()[0];
                reference_bases.push(new_bp);
            }
            for bit in &block_bits[250..] {
                bit.enforce_equal(&Boolean::<F>::FALSE).unwrap();
            }
        }

        let mut target_bases = Vec::new();
        for block in target_sequence_vars {
            let block_bits = &block.to_bits_le().unwrap();
            let mut chunks = block_bits[0..250].chunks_exact(2);
            for bit_pair in chunks.by_ref().take(BASES_PER_BLOCK) {
                let new_bp = &bit_pair[0].to_constraint_field().unwrap()[0] + &two * &bit_pair[1].to_constraint_field().unwrap()[0];
                target_bases.push(new_bp);
            }
            for bit in &block_bits[250..] {
                bit.enforce_equal(&Boolean::<F>::FALSE).unwrap();
            }
        }

        let mut cigar_chars = Vec::new();
        for block in cigar_string_vars {
            let block_bits = &block.to_bits_le().unwrap();
            let mut chunks = block_bits[0..250].chunks_exact(2);
            for bit_pair in chunks.by_ref().take(BASES_PER_BLOCK) {
                let new_bp = &bit_pair[0].to_constraint_field().unwrap()[0] + &two * &bit_pair[1].to_constraint_field().unwrap()[0];
                cigar_chars.push(new_bp);
            }
            for bit in &block_bits[250..] {
                bit.enforce_equal(&Boolean::<F>::FALSE).unwrap();
            }
        }

        let mut target_string_memcheck_prod_1 = FpVar::new_constant(cs.clone(), F::one()).unwrap();
        let mut reference_string_memcheck_prod_1 = FpVar::new_constant(cs.clone(), F::one()).unwrap();
        let mut i_felt = F::zero();
        for i in 0..reference_bases.len() {
            target_string_memcheck_prod_1 *= &challenge_vars[0] + &target_bases[i] + FpVar::new_constant(cs.clone(), i_felt).unwrap() * &challenge_vars[1];
            reference_string_memcheck_prod_1 *= &challenge_vars[0] + &reference_bases[i] + FpVar::new_constant(cs.clone(), i_felt).unwrap() * &challenge_vars[1];
            i_felt += F::one();
        }

        // Constants
        let alignment_match = FpVar::new_constant(cs.clone(), F::zero()).unwrap();
        let insertion = FpVar::new_constant(cs.clone(), F::one()).unwrap();
        let deletion = FpVar::new_constant(cs.clone(), F::one() + F::one()).unwrap();


        let mut target_index_var = FpVar::new_constant(cs.clone(), F::zero()).unwrap();
        let mut reference_index_var = FpVar::new_constant(cs.clone(), F::zero()).unwrap();
        let mut target_index = 0usize;
        let mut reference_index = 0usize;
        let mut target_string_memcheck_prod_2 = FpVar::new_constant(cs.clone(), F::one()).unwrap();
        let mut reference_string_memcheck_prod_2 = FpVar::new_constant(cs.clone(), F::one()).unwrap();
        let mut alignment_score = FpVar::new_constant(cs.clone(), F::zero()).unwrap();
        for i in 0..cigar_chars.len() {
            let is_match = cigar_chars[i].is_eq(&alignment_match).unwrap();
            let is_insertion = cigar_chars[i].is_eq(&insertion).unwrap();
            let is_deletion = cigar_chars[i].is_eq(&deletion).unwrap();
            alignment_score += &is_deletion.to_constraint_field().unwrap()[0] + &is_insertion.to_constraint_field().unwrap()[0];

            // TODO: convert the strings of felts into strings of base pairs
            // as part of the struct (or this function). For now don't compute an alignment and just assume it's 
            // 100% match.
            let target_sequence_read_val = FpVar::new_witness(cs.clone(), || Ok(usize_to_felt::<F>(self.target_sequence_bases[i]))).unwrap();
            let reference_sequence_read_val = FpVar::new_witness(cs.clone(), || Ok(usize_to_felt::<F>(self.reference_sequence_bases[i]))).unwrap();

            // if is_match, bases_match must be true. if not is match either is fine.
            let bases_match = target_sequence_read_val.is_eq(&reference_sequence_read_val).unwrap();
            is_match.not().or(&bases_match).unwrap().enforce_equal(&Boolean::<F>::TRUE).unwrap();

            target_string_memcheck_prod_2 *= (&is_match.or(&is_insertion).unwrap()).select(&(&challenge_vars[0] + &target_sequence_read_val + &target_index_var * &challenge_vars[1]), &FpVar::new_constant(cs.clone(), F::one()).unwrap()).unwrap();
            reference_string_memcheck_prod_2 *= (&is_match.or(&is_deletion).unwrap()).select(&(&challenge_vars[0] + &reference_sequence_read_val + &reference_index_var * &challenge_vars[1]), &FpVar::new_constant(cs.clone(), F::one()).unwrap()).unwrap();

            target_index_var += (&is_match.to_constraint_field().unwrap()[0] + &is_insertion.to_constraint_field().unwrap()[0]);
            reference_index_var += &is_match.to_constraint_field().unwrap()[0] + &is_deletion.to_constraint_field().unwrap()[0];
            match self.cigar_string_bases[i] {
                0 => {target_index+=1; reference_index +=1},
                1 => {target_index+=1;},
                2 => {reference_index +=1},
                _ => {panic!("Witness generation reached an incorrect CIGAR character")}
            }
        }

        target_string_memcheck_prod_1.enforce_equal(&target_string_memcheck_prod_2).unwrap();
        reference_string_memcheck_prod_1.enforce_equal(&reference_string_memcheck_prod_2).unwrap();

        let res_score = FpVar::<F>::new_input(cs.clone(), || Ok(F::from_le_bytes_mod_order(&self.alignment_score.to_le_bytes())))?;
        res_score.enforce_equal(&alignment_score).unwrap();

        Ok(())
    }
}

fn generate_random_sequence(bases: usize) -> (Vec<Fr>, Vec<usize>) {
    let rng = &mut ark_std::test_rng();
    let random_bools = (0..bases).map(|_| vec![rng.gen_bool(0.5), rng.gen_bool(0.5)]).collect::<Vec<_>>();
    let random_bases = random_bools.clone().into_iter().map(|x| (x[1] as usize) * 2 + (x[0] as usize)).collect::<Vec<_>>();

    let random_felts = 
            random_bools.clone()
                .into_iter()
                .flatten()
                .collect::<Vec<_>>()
                .chunks(BASES_PER_BLOCK * 2)
                .map(|x| {
                    let mut x_vec = vec![];
                    let five_false =  vec![false; 5]; // need to pad x with 0's so this behaves as expected.
                    x_vec.extend_from_slice(x);
                    x_vec.extend_from_slice(&five_false);
                    Fr::from_bigint(BigInt::from_bits_le(&x_vec)).unwrap()})
                .collect();
    (random_felts, random_bases)
}

fn usize_to_felt<F: PrimeField>(base: usize) -> F {
    match base {
        0 => F::zero(),
        1 => F::one(),
        2 => F::one() + F::one(),
        3 => F::one() + F::one() + F::one(),
        _ => panic!("bad base number provided"),
    }
}

fn main() {
    // For benchmarking, just verify the alignment of 2 identical sequences, I did correctness testing separately.
    // zk proofs are a uniform model of computation so data used is not overly important.
    let (reference_sequence_felts, reference_sequence_bases) = generate_random_sequence(SEQUENCE_BASE_PAIRS);
    let (target_sequence_felts, target_sequence_bases) = (reference_sequence_felts.clone(), reference_sequence_bases.clone());

    let cigar_string_felts: Vec<_> = (0..CIGAR_STRING_LENGTH_BLOCKS).map(|_| Fr::zero()).collect();
    let cigar_string_letters = (0..CIGAR_STRING_LENGTH).map(|_| 0).collect::<Vec<_>>();
    let alignment_score = 0;

    println!("Sequence length is: {}", SEQUENCE_BASE_PAIRS);

    let c = AlignmentCircuit::<Fr>::new(reference_sequence_felts.clone(), reference_sequence_bases.clone(), target_sequence_felts.clone(), target_sequence_bases.clone(), cigar_string_felts.clone(), cigar_string_letters.clone(), alignment_score);
    {
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);

        let mut circuit = c.clone();
        let mut cs = ConstraintSystem::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();
        println!("Num constraints: {:?}", cs.num_constraints());
        // Let's check whether the constraint system is satisfied
        let is_satisfied = cs.is_satisfied().unwrap();
        if !is_satisfied {
            // If it isn't, find out the offending constraint.
            println!("{:?}", cs.which_is_unsatisfied());
        }
    }

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    let start = ark_std::time::Instant::now();
    let (pk, vk) = Groth16::<Bls12_381>::setup(c.clone(), &mut rng).unwrap();
    let pvk = Groth16::<Bls12_381>::process_vk(&vk).unwrap();
    println!(
        "setup time for BLS12-381: {} s",
        start.elapsed().as_secs_f64()
    );

    let start = ark_std::time::Instant::now();
    let proof = Groth16::<Bls12_381>::prove(&pk, c, &mut rng).unwrap();
    println!(
        "proving time for BLS12-381: {} s",
        start.elapsed().as_secs_f64()
    );

    let start = ark_std::time::Instant::now();
    assert!(Groth16::<Bls12_381>::verify_with_processed_vk(&pvk, &[Fr::zero()], &proof).unwrap());
    println!(
        "verification time for BLS12-381: {} s",
        start.elapsed().as_secs_f64()
    );
}
