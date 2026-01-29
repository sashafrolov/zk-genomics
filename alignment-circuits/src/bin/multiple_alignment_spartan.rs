//! examples/basic_alignment_spartan.rs
//! Spartan version of the alignment circuit previously written
//! in Arkworks. Similar, just a lot faster.
//!
#![allow(non_snake_case)]
#[cfg(feature = "jem")]
#[global_allocator]
static GLOBAL: Jemalloc = tikv_jemallocator::Jemalloc;
use bellpepper::gadgets::boolean::field_into_allocated_bits_le;
use bellpepper_core::{
    ConstraintSystem, LinearCombination, SynthesisError,
    num::AllocatedNum,
};
use ff::{Field, PrimeField, PrimeFieldBits};
use generic_array::typenum::U2;
use neptune::sponge::{
    api::{IOPattern, SpongeAPI, SpongeOp},
    circuit::SpongeCircuit,
    vanilla::{Mode, Sponge, SpongeTrait},
};
use neptune::{Strength, circuit2::Elt};
use spartan2::{
    provider::T256HyraxEngine,
    spartan::SpartanSNARK,
    traits::{Engine, circuit::SpartanCircuit, snark::R1CSSNARKTrait},
};
use std::{marker::PhantomData, time::Instant};
use tracing::{info, info_span};
use tracing_subscriber::EnvFilter;

use alignment_circuits::alignment_plain_computation::msa_pairwise_cost;
use alignment_circuits::{Base, MSACigarChar, ToFeltBlocks};

type E = T256HyraxEngine;

const BASES_PER_BLOCK: usize = 125;
const SEQUENCE_BLOCK_LENGTH: usize = 1 << 6;
const SEQUENCE_BASE_PAIRS: usize = SEQUENCE_BLOCK_LENGTH * BASES_PER_BLOCK;
const ADVICE_STRING_LENGTH: usize = SEQUENCE_BASE_PAIRS;
const ADVICE_STRING_LENGTH_BLOCKS: usize = SEQUENCE_BASE_PAIRS.div_ceil(BASES_PER_BLOCK*2);
const NUM_SEQUENCES: usize = 4;
const NUM_PAIRS: usize = NUM_SEQUENCES * (NUM_SEQUENCES - 1) / 2;

// Instance of multiple sequence alignment. We set the 0th sequence to be the public input/reference.
#[derive(Clone, Debug)]
struct MultipleAlignmentCircuit<Scalar: PrimeField> {
    pub sequences_felts: Vec<Vec<Scalar>>, // The sequences being aligned
    pub sequences_bases: Vec<Vec<Base>>, // The sequences being aligned, as bases.
    pub advice_string_felts: Vec<Vec<Scalar>>,
    pub advice_string_chars: Vec<Vec<MSACigarChar>>,
    pub alignment_score: usize, // claimed alignment score which is a public output. 0 is perfect, +1 for each mismatch, matching the existing zkMSA repo.

    _p: PhantomData<Scalar>,
}

impl<Scalar: PrimeField + PrimeFieldBits> MultipleAlignmentCircuit<Scalar> {
    fn new(sequences_bases: Vec<Vec<Base>>, advice_string_chars: Vec<Vec<MSACigarChar>>) -> Self {
        assert!(sequences_bases.len() == NUM_SEQUENCES);
        assert!(advice_string_chars.len() == NUM_SEQUENCES);

        let sequences_felts: Vec<Vec<Scalar>> = sequences_bases
            .iter()
            .map(|seq| seq.to_felt_blocks::<Scalar>(BASES_PER_BLOCK))
            .collect();

        let advice_string_felts: Vec<Vec<Scalar>> = advice_string_chars
            .iter()
            .map(|seq| seq.to_felt_blocks::<Scalar>(BASES_PER_BLOCK))
            .collect();

        let alignment_score = msa_pairwise_cost(&sequences_bases, &advice_string_chars, 1.0);
        
        Self {
            sequences_felts,
            sequences_bases,
            advice_string_felts,
            advice_string_chars,
            alignment_score: (alignment_score as usize),
            _p: PhantomData,
        }
    }
}

impl<E: Engine> SpartanCircuit<E> for MultipleAlignmentCircuit<E::Scalar> {
    fn public_values(&self) -> Result<Vec<<E as Engine>::Scalar>, SynthesisError> {
        let mut public_values = Vec::new();

        // Define the first sequence to be the public one.
        for block in &self.sequences_felts[0] {
            public_values.push(block.clone());
        }

        let public_score = <E as Engine>::Scalar::from_u128((self.alignment_score) as u128);
        public_values.push(public_score);

        Ok(public_values)
    }

    fn shared<CS: ConstraintSystem<E::Scalar>>(
        &self,
        _: &mut CS,
    ) -> Result<Vec<AllocatedNum<E::Scalar>>, SynthesisError> {
        // No shared variables in this circuit
        Ok(vec![])
    }

    fn precommitted<CS: ConstraintSystem<E::Scalar>>(
        &self,
        cs: &mut CS,
        _: &[AllocatedNum<E::Scalar>], // shared variables, if any
    ) -> Result<Vec<AllocatedNum<E::Scalar>>, SynthesisError> {
        // 1. Allocate all sequence inputs
        let mut sequences_input_vars: Vec<Vec<AllocatedNum<E::Scalar>>> = Vec::new();
        for (seq_idx, seq_felts) in self.sequences_felts.iter().enumerate() {
            let mut seq_vars = Vec::new();
            for (block_idx, block) in seq_felts.iter().enumerate() {
                seq_vars.push(AllocatedNum::alloc(
                    cs.namespace(|| format!("Sequence {seq_idx} block {block_idx}")),
                    || Ok(*block),
                )?);
            }
            sequences_input_vars.push(seq_vars);
        }

        let mut sequences_base_vars: Vec<Vec<AllocatedNum<E::Scalar>>> = Vec::new();
        for (seq_idx, seq_bases) in self.sequences_bases.iter().enumerate() {
            let mut seq_vars = Vec::new();
            for (base_idx, base) in seq_bases.iter().enumerate() {
                seq_vars.push(AllocatedNum::alloc(
                    cs.namespace(|| format!("Sequence {seq_idx} base {base_idx}")),
                    || Ok(base.to_field()),
                )?);
            }
            sequences_base_vars.push(seq_vars);
        }

        // Allocate public input blocks for the first sequence
        let mut first_sequence_public_vars = Vec::new();
        for (block_idx, block) in self.sequences_felts[0].iter().enumerate() {
            first_sequence_public_vars.push(AllocatedNum::alloc_input(
                cs.namespace(|| format!("Public reference sequence block {block_idx}")),
                || Ok(*block),
            )?);
        }

        // Enforce equality between public inputs and the first sequence's blocks
        for (block_idx, (public_var, private_var)) in first_sequence_public_vars
            .iter()
            .zip(sequences_input_vars[0].iter())
            .enumerate()
        {
            cs.enforce(
                || format!("Reference sequence block {block_idx} public-private equality"),
                |lc| lc + public_var.get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + private_var.get_variable(),
            );
        }

        let mut cigar_string_input_vars: Vec<Vec<AllocatedNum<E::Scalar>>> = Vec::new();
        for (seq_idx, seq_felts) in self.advice_string_felts.iter().enumerate() {
            let mut seq_vars = Vec::new();
            for (block_idx, block) in seq_felts.iter().enumerate() {
                seq_vars.push(AllocatedNum::alloc(
                    cs.namespace(|| format!("Cigar string {seq_idx} block {block_idx}")),
                    || Ok(*block),
                )?);
            }
            cigar_string_input_vars.push(seq_vars);
        }

        let mut cigar_string_char_vars: Vec<Vec<AllocatedNum<E::Scalar>>> = Vec::new();
        for (seq_idx, seq_chars) in self.advice_string_chars.iter().enumerate() {
            let mut seq_vars = Vec::new();
            for (char_idx, char) in seq_chars.iter().enumerate() {
                seq_vars.push(AllocatedNum::alloc(
                    cs.namespace(|| format!("Cigar string {seq_idx} char {char_idx}")),
                    || Ok(char.to_field()),
                )?);
            }
            cigar_string_char_vars.push(seq_vars);
        }

        // The score needs to be public as well.
        let alignment_score_public =
            AllocatedNum::alloc_input(cs.namespace(|| "public alignment score"), || {
                Ok(E::Scalar::from_u128(self.alignment_score as u128))
            })?;

        // 2. Enforce that the bases are correct (this is kind of shitty in Bellpepper unfortunately):
        let TWO = E::Scalar::from(2u64);
        for (seq_idx, seq_blocks) in sequences_input_vars.iter().enumerate() {
            for (block_idx, block) in seq_blocks.iter().enumerate() {
                let block_as_bits = field_into_allocated_bits_le(
                    cs.namespace(|| format!("Sequence {seq_idx} felt block {block_idx} decomposition")),
                    Some(self.sequences_felts[seq_idx][block_idx]),
                )?;
                for j in 0..BASES_PER_BLOCK {
                    if block_idx * BASES_PER_BLOCK + j < self.sequences_bases[seq_idx].len() {
                        // Only enforce for valid bases (last block may be partial)
                        cs.enforce(
                            || {
                                format!(
                                    "Enforcing base decomposition for sequence {seq_idx} block {block_idx} base {j}"
                                )
                            },
                            |lc| lc + CS::one(),
                            |lc| {
                                lc + (TWO, block_as_bits[2 * j + 1].get_variable())
                                    + block_as_bits[2 * j].get_variable()
                            },
                            |lc| lc + sequences_base_vars[seq_idx][block_idx * BASES_PER_BLOCK + j].get_variable(),
                        );
                    } else {
                        // Ensure proper zero padding so this doesn't mess up the other constraint check.
                        cs.enforce(
                            || {
                                format!(
                                    "Enforcing zero padding for sequence {seq_idx} block {block_idx} position {j}"
                                )
                            },
                            |lc| lc + CS::one(),
                            |lc| {
                                lc + (TWO, block_as_bits[2 * j + 1].get_variable())
                                    + block_as_bits[2 * j].get_variable()
                            },
                            |lc| lc, // zero
                        );
                    }
                }
                let mut pow_of_two = E::Scalar::ONE;
                let mut overall_decomposition_lc = LinearCombination::zero();
                for bit in block_as_bits {
                    overall_decomposition_lc =
                        overall_decomposition_lc + (pow_of_two, bit.get_variable());
                    pow_of_two = pow_of_two * TWO;
                }

                cs.enforce(
                    || format!("Enforcing overall bit decomposition for sequence {seq_idx} block {block_idx}"),
                    |lc| lc + CS::one(),
                    |lc| lc + &overall_decomposition_lc,
                    |lc| lc + block.get_variable(),
                );
            }
        }

        for (seq_idx, seq_blocks) in cigar_string_input_vars.iter().enumerate() {
            for (block_idx, block) in seq_blocks.iter().enumerate() {
                let block_as_bits = field_into_allocated_bits_le(
                    cs.namespace(|| format!("Cigar string {seq_idx} felt block {block_idx} decomposition")),
                    Some(self.advice_string_felts[seq_idx][block_idx]),
                )?;
                for j in 0..BASES_PER_BLOCK {
                    if block_idx * BASES_PER_BLOCK + j < self.advice_string_chars[seq_idx].len() {
                        // Only enforce for valid chars (last block may be partial)
                        cs.enforce(
                            || format!("Enforcing char decomposition for cigar {seq_idx} block {block_idx} char {j}"),
                            |lc| lc + CS::one(),
                            |lc| {
                                lc + (TWO, block_as_bits[2 * j + 1].get_variable())
                                    + block_as_bits[2 * j].get_variable()
                            },
                            |lc| lc + cigar_string_char_vars[seq_idx][block_idx * BASES_PER_BLOCK + j].get_variable(),
                        );
                    } else {
                        // Ensure proper zero padding so this doesn't mess up the other constraint check.
                        cs.enforce(
                            || format!("Enforcing zero padding for cigar {seq_idx} block {block_idx} position {j}"),
                            |lc| lc + CS::one(),
                            |lc| {
                                lc + (TWO, block_as_bits[2 * j + 1].get_variable())
                                    + block_as_bits[2 * j].get_variable()
                            },
                            |lc| lc, // zero
                        );
                    }
                }
                let mut pow_of_two = E::Scalar::ONE;
                let mut overall_decomposition_lc = LinearCombination::zero();
                for bit in block_as_bits {
                    overall_decomposition_lc =
                        overall_decomposition_lc + (pow_of_two, bit.get_variable());
                    pow_of_two = pow_of_two * TWO;
                }

                cs.enforce(
                    || format!("Enforcing overall bit decomposition for cigar {seq_idx} block {block_idx}"),
                    |lc| lc + CS::one(),
                    |lc| lc + &overall_decomposition_lc,
                    |lc| lc + block.get_variable(),
                );
            }
        }

        // 3. Compute a hash for random challenges (will remove this part later in favor of random challenges from Spartan itself.)
        let (memcheck_challenge_0, memcheck_challenge_1) = {
            let default_poseidon_params =
                Sponge::<<E as Engine>::Scalar, U2>::api_constants(Strength::Standard);
            let mut sponge = SpongeCircuit::<<E as Engine>::Scalar, U2, _>::new_with_constants(
                &default_poseidon_params,
                Mode::Simplex,
            );

            let poseidon_hash_input_len =
                self.sequences_felts.len() * self.sequences_felts[0].len() + self.advice_string_felts.len() * self.advice_string_felts[0].len();
            let parameter = IOPattern(vec![
                SpongeOp::Absorb(poseidon_hash_input_len as u32),
                SpongeOp::Squeeze(2),
            ]);

            let ns = &mut cs.namespace(|| "Poseidon Sponge Start");

            sponge.start(parameter, None, ns);

            let preimage_felts_reallocated: Vec<Elt<<E as Engine>::Scalar>> =
                sequences_input_vars
                    .into_iter()
                    .flatten()
                    .chain(cigar_string_input_vars.into_iter().flatten())
                    .map(|s| Elt::Allocated(s))
                    .collect();

            SpongeAPI::absorb(
                &mut sponge,
                poseidon_hash_input_len as u32,
                preimage_felts_reallocated.as_slice(),
                ns,
            );

            let calc_node = SpongeAPI::squeeze(&mut sponge, 2, ns);

            assert_eq!(calc_node.len(), 2);

            sponge.finish(ns).unwrap();

            let chall_0 =
                calc_node[0].ensure_allocated(&mut ns.namespace(|| "Challenge 0"), true)?;
            let chall_1 =
                calc_node[1].ensure_allocated(&mut ns.namespace(|| "Challenge 1"), true)?;
            (chall_0, chall_1)
        };

        // 4. Verify alignment:

        // Initialize LHS of memcheck products for each pair of sequences
        // Each pair (seq_1, seq_2) needs two memcheck products: one for seq_1 bases, one for seq_2 bases
        let mut left_memcheck_products_1: Vec<AllocatedNum<E::Scalar>> = Vec::new();
        let mut left_memcheck_products_2: Vec<AllocatedNum<E::Scalar>> = Vec::new();

        for seq_1_id in 0..NUM_SEQUENCES {
            for seq_2_id in (seq_1_id + 1)..NUM_SEQUENCES {
                // Build left memcheck product for sequence 1 in this pair
                let mut seq1_memcheck_product_left = AllocatedNum::alloc(
                    cs.namespace(|| format!("Initial seq {seq_1_id} left memcheck product for pair ({seq_1_id}, {seq_2_id})")),
                    || Ok(E::Scalar::ONE),
                )?;
                for (i, base) in sequences_base_vars[seq_1_id].iter().enumerate() {
                    let addition_1 = base.add(
                        cs.namespace(|| format!("Left seq {seq_1_id} memcheck pair ({seq_1_id},{seq_2_id}) base {i} addition 1")),
                        &memcheck_challenge_0,
                    )?;
                    let index_var = AllocatedNum::alloc(
                        cs.namespace(|| format!("Constant var for index {i} of left seq {seq_1_id} memcheck pair ({seq_1_id},{seq_2_id})")),
                        || Ok(E::Scalar::from_u128(i as u128)),
                    )?;
                    let multiplication_1 = index_var.mul(
                        cs.namespace(|| format!("Left seq {seq_1_id} memcheck pair ({seq_1_id},{seq_2_id}) base {i} multiplication 1")),
                        &memcheck_challenge_1,
                    )?;
                    let addition_2 = multiplication_1.add(
                        cs.namespace(|| format!("Left seq {seq_1_id} memcheck pair ({seq_1_id},{seq_2_id}) base {i} addition 2")),
                        &addition_1,
                    )?;
                    seq1_memcheck_product_left = seq1_memcheck_product_left.mul(
                        cs.namespace(|| format!("Left seq {seq_1_id} memcheck pair ({seq_1_id},{seq_2_id}) base {i} multiplication 2")),
                        &addition_2,
                    )?;
                }
                left_memcheck_products_1.push(seq1_memcheck_product_left);

                // Build left memcheck product for sequence 2 in this pair
                let mut seq2_memcheck_product_left = AllocatedNum::alloc(
                    cs.namespace(|| format!("Initial seq {seq_2_id} left memcheck product for pair ({seq_1_id}, {seq_2_id})")),
                    || Ok(E::Scalar::ONE),
                )?;
                for (i, base) in sequences_base_vars[seq_2_id].iter().enumerate() {
                    let addition_1 = base.add(
                        cs.namespace(|| format!("Left seq {seq_2_id} memcheck pair ({seq_1_id},{seq_2_id}) base {i} addition 1")),
                        &memcheck_challenge_0,
                    )?;
                    let index_var = AllocatedNum::alloc(
                        cs.namespace(|| format!("Constant var index {i} for left seq {seq_2_id} memcheck pair ({seq_1_id},{seq_2_id})")),
                        || Ok(E::Scalar::from_u128(i as u128)),
                    )?;
                    let multiplication_1 = index_var.mul(
                        cs.namespace(|| format!("Left seq {seq_2_id} memcheck pair ({seq_1_id},{seq_2_id}) base {i} multiplication 1")),
                        &memcheck_challenge_1,
                    )?;
                    let addition_2 = multiplication_1.add(
                        cs.namespace(|| format!("Left seq {seq_2_id} memcheck pair ({seq_1_id},{seq_2_id}) base {i} addition 2")),
                        &addition_1,
                    )?;
                    seq2_memcheck_product_left = seq2_memcheck_product_left.mul(
                        cs.namespace(|| format!("Left seq {seq_2_id} memcheck pair ({seq_1_id},{seq_2_id}) base {i} multiplication 2")),
                        &addition_2,
                    )?;
                }
                left_memcheck_products_2.push(seq2_memcheck_product_left);
            }
        }


        // Constants
        let ONE = AllocatedNum::alloc(cs.namespace(|| "One constant"), || Ok(E::Scalar::ONE))?;
        let MINUS_ONE = AllocatedNum::alloc(cs.namespace(|| "Negative one constant"), || {
            Ok(-E::Scalar::ONE)
        })?;

        let mut right_memcheck_products_1: Vec<AllocatedNum<E::Scalar>> = Vec::new();
        let mut right_memcheck_products_2: Vec<AllocatedNum<E::Scalar>> = Vec::new();
        let mut total_alignment_score =
            AllocatedNum::alloc(cs.namespace(|| "Total alignment score quantity"), || {
                Ok(E::Scalar::ZERO)
            })?;
    
        let advice_string_length = self.advice_string_chars[0].len();
        for seq_1_id in 0..NUM_SEQUENCES {
            for seq_2_id in (seq_1_id + 1)..NUM_SEQUENCES {
                // Initialize variables that get updated in the loop
                let mut seq1_index_var =
                    AllocatedNum::alloc(cs.namespace(|| format!("Initial index into sequence 1 for pair ({seq_1_id},{seq_2_id})")), || {
                        Ok(E::Scalar::ZERO)
                    })?;
                let mut seq2_index_var = AllocatedNum::alloc(
                    cs.namespace(|| format!("Initial index into sequence 2 for pair ({seq_1_id},{seq_2_id})")),
                    || Ok(E::Scalar::ZERO),
                )?;
                let mut seq1_index = 0usize;
                let mut seq2_index = 0usize;

                let mut seq1_memcheck_product_right = AllocatedNum::alloc(
                    cs.namespace(|| format!("Initial sequence 1 right memcheck product for pair ({seq_1_id},{seq_2_id})")),
                    || Ok(E::Scalar::ONE),
                )?;
                let mut seq2_memcheck_product_right = AllocatedNum::alloc(
                    cs.namespace(|| format!("Initial sequence 2 right memcheck product for pair ({seq_1_id},{seq_2_id})")),
                    || Ok(E::Scalar::ONE),
                )?;
                let mut alignment_score =
                    AllocatedNum::alloc(cs.namespace(|| format!("Initial alignment score quantity for pair ({seq_1_id},{seq_2_id})")), || {
                        Ok(E::Scalar::ZERO)
                    })?;
                for i in 0..advice_string_length {
                    let advice_char_1 = self.advice_string_chars[seq_1_id][i];
                    let advice_char_2 = self.advice_string_chars[seq_2_id][i];

                    let advice_char_1_var = cigar_string_char_vars[seq_1_id][i].clone();
                    let advice_char_2_var = cigar_string_char_vars[seq_2_id][i].clone();

                    // Booleans corresponding to each possible CIGAR string character
                    let is_seq_1_match = AllocatedNum::alloc(
                        cs.namespace(|| format!("is_match comparison operator {i} for sequence 1, sequence pair ({seq_1_id},{seq_2_id})")),
                        || {
                            Ok(if self.advice_string_chars[seq_1_id][i] == MSACigarChar::Match {
                                E::Scalar::ONE
                            } else {
                                E::Scalar::ZERO
                            })
                        },
                    )?;
                    cs.enforce(
                        || format!("is_match equality constraint {i}  for sequence 1, sequence pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + advice_char_1_var.get_variable(), // Char will be zero when equality passes.
                        |lc| lc + is_seq_1_match.get_variable(),
                        |_| LinearCombination::zero(),
                    );
                    cs.enforce(
                        || format!("is_match booleanity constraint {i} for sequence 1, sequence pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + is_seq_1_match.get_variable(),
                        |lc| lc + CS::one() - is_seq_1_match.get_variable(),
                        |_| LinearCombination::zero(),
                    );

                    let is_seq_2_match = AllocatedNum::alloc(
                        cs.namespace(|| format!("is_match comparison operator {i} for sequence 2, sequence pair ({seq_1_id},{seq_2_id})")),
                        || {
                            Ok(if self.advice_string_chars[seq_2_id][i] == MSACigarChar::Match {
                                E::Scalar::ONE
                            } else {
                                E::Scalar::ZERO
                            })
                        },
                    )?;
                    cs.enforce(
                        || format!("is_match equality constraint {i}  for sequence 2, sequence pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + advice_char_2_var.get_variable(), // Char will be zero when equality passes.
                        |lc| lc + is_seq_2_match.get_variable(),
                        |_| LinearCombination::zero(),
                    );
                    cs.enforce(
                        || format!("is_match booleanity constraint {i}, for sequence 2, sequence pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + is_seq_2_match.get_variable(),
                        |lc| lc + CS::one() - is_seq_2_match.get_variable(),
                        |_| LinearCombination::zero(),
                    );

                    let is_seq_1_gap = AllocatedNum::alloc(
                        cs.namespace(|| format!("is_gap comparison operator {i} for sequence 1, sequence pair ({seq_1_id},{seq_2_id})")),
                        || {
                            Ok(if self.advice_string_chars[seq_1_id][i] == MSACigarChar::Gap {
                                E::Scalar::ONE
                            } else {
                                E::Scalar::ZERO
                            })
                        },
                    )?;
                    cs.enforce(
                        || format!("is_gap equality constraint {i} for sequence 1, sequence pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + advice_char_1_var.get_variable() - CS::one(), // Char will be one when equality passes.
                        |lc| lc + is_seq_1_gap.get_variable(),
                        |_| LinearCombination::zero(),
                    );
                    cs.enforce(
                        || format!("is_gap booleanity constraint {i} for sequence 1, sequence pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + is_seq_1_gap.get_variable(),
                        |lc| lc + CS::one() - is_seq_1_gap.get_variable(),
                        |_| LinearCombination::zero(),
                    );

                    let is_seq_2_gap = AllocatedNum::alloc(
                        cs.namespace(|| format!("is_gap comparison operator {i} for sequence 2, sequence pair ({seq_1_id},{seq_2_id})")),
                        || {
                            Ok(if self.advice_string_chars[seq_2_id][i] == MSACigarChar::Gap {
                                E::Scalar::ONE
                            } else {
                                E::Scalar::ZERO
                            })
                        },
                    )?;
                    cs.enforce(
                        || format!("is_gap equality constraint {i} for sequence 2, sequence pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + advice_char_2_var.get_variable() - CS::one(), // Char will be one when equality passes.
                        |lc| lc + is_seq_2_gap.get_variable(),
                        |_| LinearCombination::zero(),
                    );
                    cs.enforce(
                        || format!("is_gap booleanity constraint {i} for sequence 2, sequence pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + is_seq_2_gap.get_variable(),
                        |lc| lc + CS::one() - is_seq_2_gap.get_variable(),
                        |_| LinearCombination::zero(),
                    );

                    // Compute XOR of is_seq_1_gap and is_seq_2_gap: XOR(a, b) = a + b - 2*a*b
                    let gap_product = is_seq_1_gap.mul(
                        cs.namespace(|| format!("is_gap_mismatch product {i} for pair ({seq_1_id},{seq_2_id})")),
                        &is_seq_2_gap,
                    )?;
                    let is_gap_mismatch = AllocatedNum::alloc(
                        cs.namespace(|| format!("is_gap_mismatch {i} for pair ({seq_1_id},{seq_2_id})")),
                        || {
                            let a = self.advice_string_chars[seq_1_id][i] == MSACigarChar::Gap;
                            let b = self.advice_string_chars[seq_2_id][i] == MSACigarChar::Gap;
                            Ok(if a ^ b { E::Scalar::ONE } else { E::Scalar::ZERO })
                        },
                    )?;
                    // Constrain: is_gap_mismatch = is_seq_1_gap + is_seq_2_gap - 2 * gap_product
                    cs.enforce(
                        || format!("is_gap_mismatch constraint {i} for pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + CS::one(),
                        |lc| lc + is_gap_mismatch.get_variable(),
                        |lc| lc + is_seq_1_gap.get_variable() + is_seq_2_gap.get_variable() - (TWO, gap_product.get_variable()),
                    );

                    // Take as advice the values that we read from the sequence at various indices.
                    let seq_1_read_val = AllocatedNum::alloc(
                        cs.namespace(|| format!("Reading value from seq 1 for cigar char {i} for pair ({seq_1_id},{seq_2_id})")),
                        || Ok(self.sequences_bases[seq_1_id][seq1_index].to_field()),
                    )?;
                    let is_seq_1_read_from = &is_seq_1_match;

                    let seq_2_read_val = AllocatedNum::alloc(
                        cs.namespace(|| {
                            format!("Reading value from seq 2 for cigar char {i} for pair ({seq_1_id},{seq_2_id})")
                        }),
                        || Ok(self.sequences_bases[seq_2_id][seq2_index].to_field()),
                    )?;
                    let is_seq_2_read_from = &is_seq_2_match;

                    // Build up the memcheck polynomial root (read_val + index*chall_1 + chall_0)
                    let seq_1_memcheck_addition_1 = seq_1_read_val.add(
                        cs.namespace(|| format!("Sequence 1 right target memcheck product {i} addition 1 for pair ({seq_1_id},{seq_2_id})")),
                        &memcheck_challenge_0,
                    )?;
                    let seq_1_memcheck_multiplication_1 = seq1_index_var.mul(
                        cs.namespace(|| format!("Sequence 1 right target memcheck product {i} multiplication 1 for pair ({seq_1_id},{seq_2_id})")),
                        &memcheck_challenge_1,
                    )?;
                    let seq_1_memcheck_addition_2 = seq_1_memcheck_multiplication_1.add(
                        cs.namespace(|| format!("Sequence 1 right target memcheck product {i} addition 2 for pair ({seq_1_id},{seq_2_id})")),
                        &seq_1_memcheck_addition_1,
                    )?;

                    // Perform a select operation (if is_target_sequence_read_from then target_memcheck_addition_1 else 1
                    let seq_1_memcheck_select_addition_1 = seq_1_memcheck_addition_2.add(
                        cs.namespace(|| format!("Sequence 1 right target memcheck {i} select first addition for pair ({seq_1_id},{seq_2_id})")),
                        &MINUS_ONE,
                    )?;
                    let seq_1_memcheck_select_mul_1 = seq_1_memcheck_select_addition_1.mul(
                        cs.namespace(|| format!("Sequence 1 right target memcheck {i} select first multiplication for pair ({seq_1_id},{seq_2_id})")),
                        &is_seq_1_read_from,
                    )?;
                    let seq_1_memcheck_select_addition_2 = seq_1_memcheck_select_mul_1.add(
                        cs.namespace(|| format!("Sequence 1 right target memcheck {i} select second addition for pair ({seq_1_id},{seq_2_id})")),
                        &ONE,
                    )?;

                    seq1_memcheck_product_right = seq1_memcheck_product_right.mul(
                        cs.namespace(|| format!("Sequence 1 target memcheck product multiplication {i} for pair ({seq_1_id},{seq_2_id})")),
                        &seq_1_memcheck_select_addition_2,
                    )?;

  
                    // Build up the memcheck polynomial for seq 2
                    let seq_2_memcheck_addition_1 = seq_2_read_val.add(
                        cs.namespace(|| format!("Sequence 2 right target memcheck product {i} addition 1 for pair ({seq_1_id},{seq_2_id})")),
                        &memcheck_challenge_0,
                    )?;
                    let seq_2_memcheck_multiplication_1 = seq2_index_var.mul(
                        cs.namespace(|| format!("Sequence 2 right target memcheck product {i} multiplication 1 for pair ({seq_1_id},{seq_2_id})")),
                        &memcheck_challenge_1,
                    )?;
                    let seq_2_memcheck_addition_2 = seq_2_memcheck_multiplication_1.add(
                        cs.namespace(|| format!("Sequence 2 right target memcheck product {i} addition 2 for pair ({seq_1_id},{seq_2_id})")),
                        &seq_2_memcheck_addition_1,
                    )?;

                    // Perform a select operation (if is_target_sequence_read_from then target_memcheck_addition_1 else 1
                    let seq_2_memcheck_select_addition_1 = seq_2_memcheck_addition_2.add(
                        cs.namespace(|| format!("Sequence 2 right target memcheck {i} select first addition for pair ({seq_1_id},{seq_2_id})")),
                        &MINUS_ONE,
                    )?;
                    let seq_2_memcheck_select_mul_1 = seq_2_memcheck_select_addition_1.mul(
                        cs.namespace(|| format!("Sequence 2 right target memcheck {i} select first multiplication for pair ({seq_1_id},{seq_2_id})")),
                        &is_seq_2_read_from,
                    )?;
                    let seq_2_memcheck_select_addition_2 = seq_2_memcheck_select_mul_1.add(
                        cs.namespace(|| format!("Sequence 2 right target memcheck {i} select second addition for pair ({seq_1_id},{seq_2_id})")),
                        &ONE,
                    )?;

                    seq2_memcheck_product_right = seq2_memcheck_product_right.mul(
                        cs.namespace(|| format!("Sequence 2 target memcheck product multiplication {i} for pair ({seq_1_id},{seq_2_id})")),
                        &seq_2_memcheck_select_addition_2,
                    )?;

                    // Assert that, if the advice string says that characters match, then there is an actual match.
                    // Equality check.
                    let do_bases_match = AllocatedNum::alloc(
                        cs.namespace(|| format!("Base equality check for advice string char {i} for pair ({seq_1_id},{seq_2_id})")),
                        || {
                            Ok(
                                if self.sequences_bases[seq_1_id][seq1_index]
                                    == self.sequences_bases[seq_2_id][seq2_index]
                                {
                                    E::Scalar::ONE
                                } else {
                                    E::Scalar::ZERO
                                },
                            )
                        },
                    )?;
                    cs.enforce(
                        || format!("base equality check {i} equality constraint for pair ({seq_1_id},{seq_2_id})"),
                        |lc| {
                            lc + seq_1_read_val.get_variable()
                                - seq_2_read_val.get_variable()
                        },
                        |lc| lc + do_bases_match.get_variable(),
                        |_| LinearCombination::zero(),
                    );
                    cs.enforce(
                        || format!("base equality check {i} booleanity constraint for pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + do_bases_match.get_variable(),
                        |lc| lc + CS::one() - do_bases_match.get_variable(),
                        |_| LinearCombination::zero(),
                    );

                    // 3 way product which tells us whether to add alignment cost because 2 non gap characters and they mismatch.
                    let match_product = is_seq_1_match.mul(
                        cs.namespace(|| format!("is_proper_mismatch match product {i} for pair ({seq_1_id},{seq_2_id})")),
                        &is_seq_2_match,
                    )?;
                    let is_proper_mismatch = AllocatedNum::alloc(
                        cs.namespace(|| format!("is_proper_mismatch {i} for pair ({seq_1_id},{seq_2_id})")),
                        || {
                            let bases_match = self.sequences_bases[seq_1_id][seq1_index] == self.sequences_bases[seq_2_id][seq2_index];
                            let seq1_is_match = self.advice_string_chars[seq_1_id][i] == MSACigarChar::Match;
                            let seq2_is_match = self.advice_string_chars[seq_2_id][i] == MSACigarChar::Match;
                            Ok(if !bases_match && seq1_is_match && seq2_is_match { E::Scalar::ONE } else { E::Scalar::ZERO })
                        },
                    )?;
                    // Constrain: is_proper_mismatch = match_product * (1 - do_bases_match)
                    // Rearranged: match_product * do_bases_match = match_product - is_proper_mismatch
                    cs.enforce(
                        || format!("is_proper_mismatch constraint {i} for pair ({seq_1_id},{seq_2_id})"),
                        |lc| lc + match_product.get_variable(),
                        |lc| lc + do_bases_match.get_variable(),
                        |lc| lc + match_product.get_variable() - is_proper_mismatch.get_variable(),
                    );

                    // Update scoring function (basic sum of pairs alignment):
                    alignment_score = alignment_score.add(
                        cs.namespace(|| format!("Alignment char {i} score first addition for pair ({seq_1_id},{seq_2_id})")),
                        &is_gap_mismatch,
                    )?;
                    alignment_score = alignment_score.add(
                        cs.namespace(|| format!("Alignment char {i} score second addition for pair ({seq_1_id},{seq_2_id})")),
                        &is_proper_mismatch,
                    )?;

                    // These 3 blocks update the next index to read from in regular computation + the circuit.
                    seq1_index_var = seq1_index_var.add(
                        cs.namespace(|| format!("Alignment char {i} seq1 index update first addition for pair ({seq_1_id},{seq_2_id})")),
                        &is_seq_1_match,
                    )?;

                    seq2_index_var = seq2_index_var.add(
                        cs.namespace(|| {
                            format!("Alignment char {i} seq2 index update first addition for pair ({seq_1_id},{seq_2_id})")
                        }),
                        &is_seq_2_match,
                    )?;

                    match (self.advice_string_chars[seq_1_id][seq1_index], self.advice_string_chars[seq_2_id][seq2_index]) {
                        (MSACigarChar::Match, MSACigarChar::Match) => {
                            seq1_index += 1;
                            seq2_index += 1;
                        }
                        (MSACigarChar::Gap, MSACigarChar::Match) => {
                            seq2_index += 1;
                        }
                        (MSACigarChar::Match, MSACigarChar::Gap) => {
                            seq1_index += 1;
                        }
                        (MSACigarChar::Gap, MSACigarChar::Gap) => {
                            // Do nothing
                        }
                        _ => {
                            panic!("Witness generation reached an incorrect CIGAR character")
                        }
                    }
                }
                // Add this pair's alignment score to the total
                total_alignment_score = total_alignment_score.add(
                    cs.namespace(|| format!("Add alignment score for pair ({seq_1_id}, {seq_2_id})")),
                    &alignment_score,
                )?;

                // Push the completed right memcheck products for this pair
                right_memcheck_products_1.push(seq1_memcheck_product_right);
                right_memcheck_products_2.push(seq2_memcheck_product_right);
            }
        }

        let mut pair_index = 0;
        for seq_1_id in 0..NUM_SEQUENCES {
            for seq_2_id in (seq_1_id + 1)..NUM_SEQUENCES {
                // Enforce that the memcheck products are equal.
                cs.enforce(
                    || format!("Check that sequence 1 memcheck productsm match for alignment pair ({seq_1_id}, {seq_2_id})"),
                    |lc| {
                        lc + left_memcheck_products_1[pair_index].get_variable()
                            - right_memcheck_products_1[pair_index].get_variable()
                    },
                    |lc| lc + CS::one(),
                    |_| LinearCombination::zero(),
                );
                cs.enforce(
                    || format!("Check that sequence 2 memcheck products match for alignment pair ({seq_1_id}, {seq_2_id})"),
                    |lc| {
                        lc + left_memcheck_products_2[pair_index].get_variable()
                            - right_memcheck_products_2[pair_index].get_variable()
                    },
                    |lc| lc + CS::one(),
                    |_| LinearCombination::zero(),
                );
                pair_index += 1;
            }
        }

        // Enforce that the public alignment score matches what was computed by the circuit.
        cs.enforce(
            || format!("Check that alignment score matches public output"),
            |lc| lc + alignment_score_public.get_variable() - total_alignment_score.get_variable(),
            |lc| lc + CS::one(),
            |_| LinearCombination::zero(),
        );

        Ok(vec![])
    }

    fn num_challenges(&self) -> usize {
        0
    }

    fn synthesize<CS: ConstraintSystem<E::Scalar>>(
        &self,
        _: &mut CS,
        _: &[AllocatedNum<E::Scalar>],
        _: &[AllocatedNum<E::Scalar>],
        _: Option<&[E::Scalar]>,
    ) -> Result<(), SynthesisError> {
        Ok(())
    }
}

fn main() {
    tracing_subscriber::fmt()
        .with_target(false)
        .with_ansi(true) // no bold colour codes
        .with_env_filter(EnvFilter::from_default_env())
        .init();

    // Test 1: both sequences totally match.
    let primary_sequence_bases = Base::random_sequence(SEQUENCE_BASE_PAIRS);
    let mut aligned_sequences_bases: Vec<Vec<Base>> = Vec::new();
    aligned_sequences_bases.push(primary_sequence_bases.clone());
    for _ in 0..(NUM_SEQUENCES - 1) {
        aligned_sequences_bases.push(primary_sequence_bases.clone());
    }

    let advice_string_chars = vec![vec![MSACigarChar::Match; SEQUENCE_BASE_PAIRS]; NUM_SEQUENCES];

    let circuit = MultipleAlignmentCircuit::<<E as Engine>::Scalar>::new(
        aligned_sequences_bases,
        advice_string_chars,
    );

    // The circuit length is proportional to the CIGAR string length so this is the metric I'm using.
    let cigar_len = circuit.advice_string_chars[0].len();
    let root_span = info_span!("bench", cigar_len).entered();
    info!("======= cigar_string={} characters =======", cigar_len);

    // SETUP
    let t0 = Instant::now();
    let (pk, vk) = SpartanSNARK::<E>::setup(circuit.clone()).expect("setup failed");
    let setup_ms = t0.elapsed().as_millis();
    info!(elapsed_ms = setup_ms, "setup");
    info!("======= Constraint count is: {} =======", pk.sizes()[0]);

    // PREPARE
    let t0 = Instant::now();
    let prep_snark =
        SpartanSNARK::<E>::prep_prove(&pk, circuit.clone(), false).expect("prep_prove failed");
    let prep_ms = t0.elapsed().as_millis();
    info!(elapsed_ms = prep_ms, "prep_prove");

    // PROVE
    let t0 = Instant::now();
    let proof =
        SpartanSNARK::<E>::prove(&pk, circuit.clone(), &prep_snark, false).expect("prove failed");
    let prove_ms = t0.elapsed().as_millis();
    info!(elapsed_ms = prove_ms, "prove");

    // VERIFY
    let t0 = Instant::now();
    proof.verify(&vk).expect("verify errored");
    let verify_ms = t0.elapsed().as_millis();
    info!(elapsed_ms = verify_ms, "verify");

    // Serialize proof to measure size (not timed)
    let proof_bytes = bincode::serialize(&proof).expect("proof serialization failed");
    let proof_size_bytes = proof_bytes.len();

    // Compute public inputs size
    let public_values = <MultipleAlignmentCircuit<<E as Engine>::Scalar> as SpartanCircuit<E>>::public_values(&circuit).expect("public_values failed");
    let public_values_bytes = bincode::serialize(&public_values).expect("public_values serialization failed");
    let public_values_size_bytes = public_values_bytes.len();
    let proof_without_public_inputs = proof_size_bytes - public_values_size_bytes;

    // Summary
    info!(
        "SUMMARY cigar={} chars, setup={} ms, prep_prove={} ms, prove={} ms, verify={} ms, proof_size={} bytes, public_inputs_size={} bytes, proof_excl_public={} bytes",
        cigar_len, setup_ms, prep_ms, prove_ms, verify_ms, proof_size_bytes, public_values_size_bytes, proof_without_public_inputs
    );
    drop(root_span);
}
