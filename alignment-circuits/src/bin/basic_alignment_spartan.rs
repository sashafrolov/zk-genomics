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

use alignment_circuits::alignment_plain_computation::basic_alignment;
use alignment_circuits::{Base, CigarChar, ToFeltBlocks};

type E = T256HyraxEngine;

const BASES_PER_BLOCK: usize = 125;
// On my laptop, it looks like 1 << 9 is where memory maxes out, though proof times are still ~6 seconds, so a larger machine could go further.
const SEQUENCE_BLOCK_LENGTH: usize = 1 << 6;
const SEQUENCE_BASE_PAIRS: usize = SEQUENCE_BLOCK_LENGTH * BASES_PER_BLOCK;
// const CIGAR_STRING_LENGTH: usize = SEQUENCE_BASE_PAIRS;
// const CIGAR_STRING_LENGTH_BLOCKS: usize = SEQUENCE_BASE_PAIRS.div_ceil(BASES_PER_BLOCK);

#[derive(Clone, Debug)]
struct BasicAlignmentCircuit<Scalar: PrimeField> {
    pub reference_sequence_felts: Vec<Scalar>, // The reference for a certain gene, encoded as field elements, where BASES_PER_BLOCK bases are packed per field element
    pub reference_sequence_bases: Vec<Base>,   // Reference sequence
    pub target_sequence_felts: Vec<Scalar>,    // The sequence being aligned against the reference
    pub target_sequence_bases: Vec<Base>,
    pub cigar_string_felts: Vec<Scalar>,
    pub cigar_string_chars: Vec<CigarChar>,
    pub alignment_score: usize, // claimed alignment score which is a public output. 0 is perfect, +1 for each insertion or deletion in the basic version.

    _p: PhantomData<Scalar>,
}

impl<Scalar: PrimeField + PrimeFieldBits> BasicAlignmentCircuit<Scalar> {
    fn new(reference_sequence_bases: Vec<Base>, target_sequence_bases: Vec<Base>) -> Self {
        let reference_sequence_felts =
            reference_sequence_bases.to_felt_blocks::<Scalar>(BASES_PER_BLOCK);
        let target_sequence_felts = target_sequence_bases.to_felt_blocks::<Scalar>(BASES_PER_BLOCK);

        // We will be inverting the alignment score for public output, since Spartan likes short bitlengths.
        let (cigar_string_chars, alignment_score) = basic_alignment(
            reference_sequence_bases.clone(),
            target_sequence_bases.clone(),
            0.0,
            -1.0,
            -1.0,
        );
        let cigar_string_felts = cigar_string_chars.to_felt_blocks(BASES_PER_BLOCK);
        let positive_alignment_score = (- alignment_score) as usize;
        
        Self {
            reference_sequence_felts,
            reference_sequence_bases,
            target_sequence_felts,
            target_sequence_bases,
            cigar_string_felts,
            cigar_string_chars,
            alignment_score: positive_alignment_score,
            _p: PhantomData,
        }
    }
}

impl<E: Engine> SpartanCircuit<E> for BasicAlignmentCircuit<E::Scalar> {
    fn public_values(&self) -> Result<Vec<<E as Engine>::Scalar>, SynthesisError> {
        let mut public_values = Vec::new();

        for block in &self.reference_sequence_felts {
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
        // 1. Allocate all sequence inputs:
        let target_sequence_input_vars = self
            .target_sequence_felts
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, block)| {
                AllocatedNum::alloc(
                    cs.namespace(|| format!("Target sequence block {i}")),
                    || Ok(block),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        let target_sequence_base_vars = self
            .target_sequence_bases
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, base)| {
                AllocatedNum::alloc(cs.namespace(|| format!("Target sequence base {i}")), || {
                    Ok(base.to_field())
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        // This does embed the length of the cigar string into the circuit, with a little more work you could
        // "pad" the CIGAR string to not leak this info.
        let cigar_string_input_vars = self
            .cigar_string_felts
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, block)| {
                AllocatedNum::alloc(
                    cs.namespace(|| format!("Cigar string character block {i}")),
                    || Ok(block),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        let cigar_string_char_vars = self
            .cigar_string_chars
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, char)| {
                AllocatedNum::alloc(
                    cs.namespace(|| format!("Cigar string character {i}")),
                    || Ok(char.to_field()),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        // These are public because this is the reference.
        let reference_sequence_input_vars = self
            .reference_sequence_felts
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, block)| {
                AllocatedNum::alloc_input(
                    cs.namespace(|| format!("Reference sequence block {i}")),
                    || Ok(block),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        let reference_sequence_base_vars = self
            .reference_sequence_bases
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, base)| {
                AllocatedNum::alloc(
                    cs.namespace(|| format!("Reference sequence base {i}")),
                    || Ok(base.to_field()),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        // The score needs to be public as well.
        let alignment_score_public =
            AllocatedNum::alloc_input(cs.namespace(|| "public alignment score"), || {
                Ok(E::Scalar::from_u128(self.alignment_score as u128))
            })?;

        // 2. Enforce that the bases are correct (this is kind of shitty in Bellpepper unfortunately):
        // TODO: Factor out a function here.
        let TWO = E::Scalar::from(2u64);
        for (i, block) in target_sequence_input_vars.iter().enumerate() {
            let block_as_bits = field_into_allocated_bits_le(
                cs.namespace(|| format!("Target sequence felt block {i} decomposition")),
                Some(self.target_sequence_felts[i]),
            )?;
            for j in 0..BASES_PER_BLOCK {
                if i * BASES_PER_BLOCK + j < self.target_sequence_bases.len() {
                    // Only enforce for valid bases (last block may be partial)
                    cs.enforce(
                        || {
                            format!(
                                "Enforcing base decomposition for target sequence block {i} base {j}"
                            )
                        },
                        |lc| lc + CS::one(),
                        |lc| {
                            lc + (TWO, block_as_bits[2 * j + 1].get_variable())
                                + block_as_bits[2 * j].get_variable()
                        },
                        |lc| lc + target_sequence_base_vars[i * BASES_PER_BLOCK + j].get_variable(),
                    );
                } else {
                    // Ensure proper zero padding so this doesn't mess up the other constraint check.
                    cs.enforce(
                        || {
                            format!(
                                "Enforcing zero padding for target sequence block {i} position {j}"
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
                || format!("Enforcing overall bit decomposition for target sequence block {i}"),
                |lc| lc + CS::one(),
                |lc| lc + &overall_decomposition_lc,
                |lc| lc + block.get_variable(),
            );
        }

        for (i, block) in reference_sequence_input_vars.into_iter().enumerate() {
            let block_as_bits = field_into_allocated_bits_le(
                cs.namespace(|| format!("Reference sequence felt block {i} decomposition")),
                Some(self.reference_sequence_felts[i]),
            )?;
            for j in 0..BASES_PER_BLOCK {
                if i * BASES_PER_BLOCK + j < self.reference_sequence_bases.len() {
                    // Only enforce for valid bases (last block may be partial)
                    cs.enforce(
                        || {
                            format!(
                                "Enforcing base decomposition for reference sequence block {i} base {j}"
                            )
                        },
                        |lc| lc + CS::one(),
                        |lc| {
                            lc + (TWO, block_as_bits[2 * j + 1].get_variable())
                                + block_as_bits[2 * j].get_variable()
                        },
                        |lc| lc + reference_sequence_base_vars[i * BASES_PER_BLOCK + j].get_variable(),
                    );
                } else {
                    // Ensure proper zero padding so this doesn't mess up the other constraint check.
                    cs.enforce(
                        || {
                            format!(
                                "Enforcing zero padding for reference sequence block {i} position {j}"
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
                || format!("Enforcing overall bit decomposition for reference sequence block {i}"),
                |lc| lc + CS::one(),
                |lc| lc + &overall_decomposition_lc,
                |lc| lc + block.get_variable(),
            );
        }

        for (i, block) in cigar_string_input_vars.iter().enumerate() {
            let block_as_bits = field_into_allocated_bits_le(
                cs.namespace(|| format!("Cigar string felt block {i} decomposition")),
                Some(self.cigar_string_felts[i]),
            )?;
            for j in 0..BASES_PER_BLOCK {
                if i * BASES_PER_BLOCK + j < self.cigar_string_chars.len() {
                    // Only enforce for valid chars (last block may be partial)
                    cs.enforce(
                        || format!("Enforcing char decomposition for cigar string block {i} char {j}"),
                        |lc| lc + CS::one(),
                        |lc| {
                            lc + (TWO, block_as_bits[2 * j + 1].get_variable())
                                + block_as_bits[2 * j].get_variable()
                        },
                        |lc| lc + cigar_string_char_vars[i * BASES_PER_BLOCK + j].get_variable(),
                    );
                } else {
                    // Ensure proper zero padding so this doesn't mess up the other constraint check.
                    cs.enforce(
                        || format!("Enforcing zero padding for cigar string block {i} position {j}"),
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
                || format!("Enforcing overall bit decomposition for cigar string block {i}"),
                |lc| lc + CS::one(),
                |lc| lc + &overall_decomposition_lc,
                |lc| lc + block.get_variable(),
            );
        }

        // 3. Compute a hash for random challenges (will remove this part later in favor of challenges directly from Spartan.)
        let (memcheck_challenge_0, memcheck_challenge_1) = {
            let default_poseidon_params =
                Sponge::<<E as Engine>::Scalar, U2>::api_constants(Strength::Standard);
            let mut sponge = SpongeCircuit::<<E as Engine>::Scalar, U2, _>::new_with_constants(
                &default_poseidon_params,
                Mode::Simplex,
            );

            let poseidon_hash_input_len =
                self.target_sequence_felts.len() + self.cigar_string_felts.len();
            let parameter = IOPattern(vec![
                SpongeOp::Absorb(poseidon_hash_input_len as u32),
                SpongeOp::Squeeze(2),
            ]);

            let ns = &mut cs.namespace(|| "Poseidon Sponge Start");

            sponge.start(parameter, None, ns);

            let preimage_felts_reallocated: Vec<Elt<<E as Engine>::Scalar>> =
                target_sequence_input_vars
                    .into_iter()
                    .chain(cigar_string_input_vars.into_iter())
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

        // Initialize LHS of memcheck products
        // TODO: Replace this with zk queue checking (this currently is faster than zk RAM but slightly worse than zk stack).
        let mut target_sequence_memcheck_product_left = AllocatedNum::alloc(
            cs.namespace(|| "Initial target sequence left memcheck product"),
            || Ok(E::Scalar::ONE),
        )?;
        for (i, base) in target_sequence_base_vars.iter().enumerate() {
            let addition_1 = base.add(
                cs.namespace(|| format!("Left target memcheck product {i} addition 1")),
                &memcheck_challenge_0,
            )?;
            let index_var = AllocatedNum::alloc(
                cs.namespace(|| format!("Constant var for left target memcheck representing {i}")),
                || Ok(E::Scalar::from_u128(i as u128)),
            )?;
            let multiplication_1 = index_var.mul(
                cs.namespace(|| format!("Left target memcheck product {i} multiplication 1")),
                &memcheck_challenge_1,
            )?;
            let addition_2 = multiplication_1.add(
                cs.namespace(|| format!("Left target memcheck product {i} addition 2")),
                &addition_1,
            )?;
            target_sequence_memcheck_product_left = target_sequence_memcheck_product_left.mul(
                cs.namespace(|| format!("Left target memcheck product {i} multiplication 2")),
                &addition_2,
            )?;
        }

        let mut reference_sequence_memcheck_product_left = AllocatedNum::alloc(
            cs.namespace(|| "Initial reference sequence left memcheck product"),
            || Ok(E::Scalar::ONE),
        )?;
        for (i, base) in reference_sequence_base_vars.iter().enumerate() {
            let addition_1 = base.add(
                cs.namespace(|| format!("Left reference memcheck product {i} addition 1")),
                &memcheck_challenge_0,
            )?;
            let index_var = AllocatedNum::alloc(
                cs.namespace(|| {
                    format!("Constant var for left reference memcheck representing {i}")
                }),
                || Ok(E::Scalar::from_u128(i as u128)),
            )?;
            let multiplication_1 = index_var.mul(
                cs.namespace(|| format!("Left reference memcheck product {i} multiplication 1")),
                &memcheck_challenge_1,
            )?;
            let addition_2 = multiplication_1.add(
                cs.namespace(|| format!("Left reference memcheck product {i} addition 2")),
                &addition_1,
            )?;
            reference_sequence_memcheck_product_left = reference_sequence_memcheck_product_left
                .mul(
                    cs.namespace(|| {
                        format!("Left reference memcheck product {i} multiplication 2")
                    }),
                    &addition_2,
                )?;
        }

        // Constants
        let ONE = AllocatedNum::alloc(cs.namespace(|| "One constant"), || Ok(E::Scalar::ONE))?;
        let MINUS_ONE = AllocatedNum::alloc(cs.namespace(|| "Negative one constant"), || {
            Ok(-E::Scalar::ONE)
        })?;

        // Initialize variables that get updated in the loop
        let mut target_index_var =
            AllocatedNum::alloc(cs.namespace(|| "Initial index into target string"), || {
                Ok(E::Scalar::ZERO)
            })?;
        let mut reference_index_var = AllocatedNum::alloc(
            cs.namespace(|| "Initial index into reference string"),
            || Ok(E::Scalar::ZERO),
        )?;
        let mut target_index = 0usize;
        let mut reference_index = 0usize;
        let mut target_sequence_memcheck_product_right = AllocatedNum::alloc(
            cs.namespace(|| "Initial target sequence right memcheck product"),
            || Ok(E::Scalar::ONE),
        )?;
        let mut reference_sequence_memcheck_product_right = AllocatedNum::alloc(
            cs.namespace(|| "Initial reference sequence right memcheck product"),
            || Ok(E::Scalar::ONE),
        )?;
        let mut alignment_score =
            AllocatedNum::alloc(cs.namespace(|| "Initial alignment score quantity"), || {
                Ok(E::Scalar::ZERO)
            })?;
        // For affine gap costs: tracks if the previous character was a non-gap (Match)
        // Initialized to 1 since the "character before the first" is treated as non-gap
        let mut is_last_character_non_gap =
            AllocatedNum::alloc(cs.namespace(|| "Initial is_last_character_non_gap"), || {
                Ok(E::Scalar::ONE)
            })?;
        for (i, char) in cigar_string_char_vars.iter().enumerate() {
            // Booleans corresponding to each possible CIGAR string character
            let is_match = AllocatedNum::alloc(
                cs.namespace(|| format!("is_match comparison operator {i}")),
                || {
                    Ok(if self.cigar_string_chars[i] == CigarChar::Match {
                        E::Scalar::ONE
                    } else {
                        E::Scalar::ZERO
                    })
                },
            )?;
            cs.enforce(
                || format!("is_match equality constraint {i}"),
                |lc| lc + char.get_variable(), // Char will be zero when equality passes.
                |lc| lc + is_match.get_variable(),
                |_| LinearCombination::zero(),
            );
            cs.enforce(
                || format!("is_match booleanity constraint {i}"),
                |lc| lc + is_match.get_variable(),
                |lc| lc + CS::one() - is_match.get_variable(),
                |_| LinearCombination::zero(),
            );

            let is_insertion = AllocatedNum::alloc(
                cs.namespace(|| format!("is_insertion comparison operator {i}")),
                || {
                    Ok(if self.cigar_string_chars[i] == CigarChar::Insert {
                        E::Scalar::ONE
                    } else {
                        E::Scalar::ZERO
                    })
                },
            )?;
            cs.enforce(
                || format!("is_insertion equality constraint {i}"),
                |lc| lc + char.get_variable() - CS::one(), // Char will be one when equality passes.
                |lc| lc + is_insertion.get_variable(),
                |_| LinearCombination::zero(),
            );
            cs.enforce(
                || format!("is_insertion booleanity constraint {i}"),
                |lc| lc + is_insertion.get_variable(),
                |lc| lc + CS::one() - is_insertion.get_variable(),
                |_| LinearCombination::zero(),
            );

            let is_deletion = AllocatedNum::alloc(
                cs.namespace(|| format!("is_deletion comparison operator {i}")),
                || {
                    Ok(if self.cigar_string_chars[i] == CigarChar::Delete {
                        E::Scalar::ONE
                    } else {
                        E::Scalar::ZERO
                    })
                },
            )?;
            cs.enforce(
                || format!("is_deletion equality constraint {i}"),
                |lc| lc + char.get_variable() - CS::one() - CS::one(), // Char will be two when equality passes.
                |lc| lc + is_deletion.get_variable(),
                |_| LinearCombination::zero(),
            );
            cs.enforce(
                || format!("is_deletion booleanity constraint {i}"),
                |lc| lc + is_deletion.get_variable(),
                |lc| lc + CS::one() - is_deletion.get_variable(),
                |_| LinearCombination::zero(),
            );

            // Update scoring function (basic alignment):
            alignment_score = alignment_score.add(
                cs.namespace(|| format!("Alignment char {i} score first addition")),
                &is_insertion,
            )?;
            alignment_score = alignment_score.add(
                cs.namespace(|| format!("Alignment char {i} score second addition")),
                &is_deletion,
            )?;

            // Update scoring function (affine gap costs):
            // Gap opening (first gap after match) costs 2, gap extension costs 1
            // Formula: is_last_character_non_gap * (is_insertion + is_deletion) + is_insertion + is_deletion
            // let is_gap = is_insertion.add(
            //     cs.namespace(|| format!("Affine gap {i}: is_gap computation")),
            //     &is_deletion,
            // )?;
            // let gap_opening_cost = is_last_character_non_gap.mul(
            //     cs.namespace(|| format!("Affine gap {i}: gap opening cost")),
            //     &is_gap,
            // )?;
            // alignment_score = alignment_score.add(
            //     cs.namespace(|| format!("Affine gap {i}: add gap opening cost")),
            //     &gap_opening_cost,
            // )?;
            // alignment_score = alignment_score.add(
            //     cs.namespace(|| format!("Affine gap {i}: add gap extension cost")),
            //     &is_gap,
            // )?;
            // // Update is_last_character_non_gap for next iteration
            // is_last_character_non_gap = is_match.clone();

            // Take as advice the values that we read from the sequence at various indices.
            let target_sequence_read_val = AllocatedNum::alloc(
                cs.namespace(|| format!("Reading value from target sequence for cigar char {i}")),
                || Ok(self.target_sequence_bases[target_index].to_field()),
            )?;
            let reference_sequence_read_val = AllocatedNum::alloc(
                cs.namespace(|| {
                    format!("Reading value from reference sequence for cigar char {i}")
                }),
                || Ok(self.reference_sequence_bases[reference_index].to_field()),
            )?;

            // Update the memcheck products with the read values.
            let is_target_sequence_read_from = (self.cigar_string_chars[i] == CigarChar::Match)
                || (self.cigar_string_chars[i] == CigarChar::Insert);
            let is_target_sequence_read_from_bit = AllocatedNum::alloc(
                cs.namespace(|| format!("Is target sequence read from index {i}")),
                || {
                    Ok(if is_target_sequence_read_from {
                        E::Scalar::ONE
                    } else {
                        E::Scalar::ZERO
                    })
                },
            )?;
            // Enforce OR constraint (rearranging a + b - a*b = a || b)
            cs.enforce(
                || format!("Enforcing OR constraint for target sequence is read from bit {i}"),
                |lc| lc + is_match.get_variable(),
                |lc| lc + is_insertion.get_variable(),
                |lc| {
                    lc + is_match.get_variable() + is_insertion.get_variable()
                        - is_target_sequence_read_from_bit.get_variable()
                },
            );
            // Build up the memcheck polynomial root (read_val + index*chall_1 + chall_0)
            let target_memcheck_addition_1 = target_sequence_read_val.add(
                cs.namespace(|| format!("Right target memcheck product {i} addition 1")),
                &memcheck_challenge_0,
            )?;
            let target_memcheck_multiplication_1 = target_index_var.mul(
                cs.namespace(|| format!("Right target memcheck product {i} multiplication 1")),
                &memcheck_challenge_1,
            )?;
            let target_memcheck_addition_2 = target_memcheck_multiplication_1.add(
                cs.namespace(|| format!("Right target memcheck product {i} addition 2")),
                &target_memcheck_addition_1,
            )?;

            // Perform a select operation (if is_target_sequence_read_from then target_memcheck_addition_1 else 1
            let target_memcheck_select_addition_1 = target_memcheck_addition_2.add(
                cs.namespace(|| format!("Right target memcheck {i} select first addition")),
                &MINUS_ONE,
            )?;
            let target_memcheck_select_mul_1 = target_memcheck_select_addition_1.mul(
                cs.namespace(|| format!("Right target memcheck {i} select first multiplication")),
                &is_target_sequence_read_from_bit,
            )?;
            let target_memcheck_select_addition_2 = target_memcheck_select_mul_1.add(
                cs.namespace(|| format!("Right target memcheck {i} select second addition")),
                &ONE,
            )?;

            target_sequence_memcheck_product_right = target_sequence_memcheck_product_right.mul(
                cs.namespace(|| format!("Right target memcheck product multiplication {i}")),
                &target_memcheck_select_addition_2,
            )?;

            let is_reference_sequence_read_from = (self.cigar_string_chars[i] == CigarChar::Match)
                || (self.cigar_string_chars[i] == CigarChar::Delete);
            let is_reference_sequence_read_from_bit = AllocatedNum::alloc(
                cs.namespace(|| format!("Is reference sequence read from index {i}")),
                || {
                    Ok(if is_reference_sequence_read_from {
                        E::Scalar::ONE
                    } else {
                        E::Scalar::ZERO
                    })
                },
            )?;
            // Enforce OR constraint (rearranging a + b - a*b = a || b)
            cs.enforce(
                || format!("Enforcing OR constraint for reference sequence is read from bit {i}"),
                |lc| lc + is_match.get_variable(),
                |lc| lc + is_deletion.get_variable(),
                |lc| {
                    lc + is_match.get_variable() + is_deletion.get_variable()
                        - is_reference_sequence_read_from_bit.get_variable()
                },
            );
            // Build up the memcheck polynomial root (read_val + index*chall_1 + chall_0)
            let reference_memcheck_addition_1 = reference_sequence_read_val.add(
                cs.namespace(|| format!("Right reference memcheck product {i} addition 1")),
                &memcheck_challenge_0,
            )?;
            let reference_memcheck_multiplication_1 = reference_index_var.mul(
                cs.namespace(|| format!("Right reference memcheck product {i} multiplication 1")),
                &memcheck_challenge_1,
            )?;
            let reference_memcheck_addition_2 = reference_memcheck_multiplication_1.add(
                cs.namespace(|| format!("Right reference memcheck product {i} addition 2")),
                &reference_memcheck_addition_1,
            )?;

            // Perform a select operation (if is_target_sequence_read_from then target_memcheck_addition_1 else 1
            let reference_memcheck_select_addition_1 = reference_memcheck_addition_2.add(
                cs.namespace(|| format!("Right reference memcheck {i} select first addition")),
                &MINUS_ONE,
            )?;
            let reference_memcheck_select_mul_1 = reference_memcheck_select_addition_1.mul(
                cs.namespace(|| {
                    format!("Right reference memcheck {i} select first multiplication")
                }),
                &is_reference_sequence_read_from_bit,
            )?;
            let reference_memcheck_select_addition_2 = reference_memcheck_select_mul_1.add(
                cs.namespace(|| format!("Right reference memcheck {i} select second addition")),
                &ONE,
            )?;

            reference_sequence_memcheck_product_right = reference_sequence_memcheck_product_right
                .mul(
                cs.namespace(|| format!("Right reference memcheck product multiplication {i}")),
                &reference_memcheck_select_addition_2,
            )?;

            // Assert that, if the CIGAR string says that characters match, then there is an actual match.
            // Equality check.
            let do_bases_match = AllocatedNum::alloc(
                cs.namespace(|| format!("Base equality check for cigar char {i}")),
                || {
                    Ok(
                        if self.target_sequence_bases[target_index]
                            == self.reference_sequence_bases[reference_index]
                        {
                            E::Scalar::ONE
                        } else {
                            E::Scalar::ZERO
                        },
                    )
                },
            )?;
            cs.enforce(
                || format!("base equality check {i} equality constraint"),
                |lc| {
                    lc + target_sequence_read_val.get_variable()
                        - reference_sequence_read_val.get_variable()
                },
                |lc| lc + do_bases_match.get_variable(),
                |_| LinearCombination::zero(),
            );
            cs.enforce(
                || format!("base equality check {i} booleanity constraint"),
                |lc| lc + do_bases_match.get_variable(),
                |lc| lc + CS::one() - do_bases_match.get_variable(),
                |_| LinearCombination::zero(),
            );
            // Actual enforcement check. Assert that (!is_match) | bases_match is true.
            cs.enforce(
                || format!("Conditional match check for CIGAR char {i}"),
                |lc| lc + is_match.get_variable(),
                |lc| lc + CS::one() - do_bases_match.get_variable(),
                |_| LinearCombination::zero(),
            );

            // These 3 blocks update the next index to read from in regular computation + the circuit.
            target_index_var = target_index_var.add(
                cs.namespace(|| format!("Alignment char {i} target index update first addition")),
                &is_match,
            )?;
            target_index_var = target_index_var.add(
                cs.namespace(|| format!("Alignment char {i} target index update second addition")),
                &is_insertion,
            )?;

            reference_index_var = reference_index_var.add(
                cs.namespace(|| {
                    format!("Alignment char {i} reference index update first addition")
                }),
                &is_match,
            )?;
            reference_index_var = reference_index_var.add(
                cs.namespace(|| {
                    format!("Alignment char {i} reference index update second addition")
                }),
                &is_deletion,
            )?;

            match self.cigar_string_chars[i] {
                CigarChar::Match => {
                    target_index += 1;
                    reference_index += 1
                }
                CigarChar::Insert => {
                    target_index += 1;
                }
                CigarChar::Delete => reference_index += 1,
                _ => {
                    panic!("Witness generation reached an incorrect CIGAR character")
                }
            }
        }

        // Enforce that the memcheck products are equal.
        cs.enforce(
            || format!("Check that the target string memcheck products match"),
            |lc| {
                lc + target_sequence_memcheck_product_left.get_variable()
                    - target_sequence_memcheck_product_right.get_variable()
            },
            |lc| lc + CS::one(),
            |_| LinearCombination::zero(),
        );
        cs.enforce(
            || format!("Check that the reference string memcheck products match"),
            |lc| {
                lc + reference_sequence_memcheck_product_left.get_variable()
                    - reference_sequence_memcheck_product_right.get_variable()
            },
            |lc| lc + CS::one(),
            |_| LinearCombination::zero(),
        );

        // Enforce that the public alignment score matches what was computed by the circuit.
        cs.enforce(
            || format!("Check that alignment score matches public output"),
            |lc| lc + alignment_score_public.get_variable() - alignment_score.get_variable(),
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

    // Test 1: both sequences totally match (used for benchmarking).
    let reference_sequence_bases = Base::random_sequence(SEQUENCE_BASE_PAIRS);
    let target_sequence_bases = reference_sequence_bases.clone();

    // Test 2: The sequences differ in their first character.
    // let reference_sequence_bases = Base::random_sequence(SEQUENCE_BASE_PAIRS);
    // let mut target_sequence_bases = reference_sequence_bases.clone();
    // // Make the first base different
    // target_sequence_bases[0] = match reference_sequence_bases[0] {
    //     Base::A => Base::C,
    //     Base::C => Base::G,
    //     Base::G => Base::T,
    //     Base::T => Base::A,
    // };

    // Test 3: both 1 outright deletion.
    // let reference_sequence_bases = Base::random_sequence(SEQUENCE_BASE_PAIRS);
    // let target_sequence_bases = reference_sequence_bases[1..].to_vec();

    // Test 4: Not multiple of 125 (this is a test case because this was previously a limitation):
    // let reference_sequence_bases = Base::random_sequence(SEQUENCE_BASE_PAIRS-22);
    // let target_sequence_bases = reference_sequence_bases.clone();


    let circuit = BasicAlignmentCircuit::<<E as Engine>::Scalar>::new(
        reference_sequence_bases,
        target_sequence_bases,
    );

    // The circuit length is proportional to the CIGAR string length so this is the metric I'm using.
    let cigar_len = circuit.cigar_string_chars.len();
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
    let public_values = <BasicAlignmentCircuit<<E as Engine>::Scalar> as SpartanCircuit<E>>::public_values(&circuit).expect("public_values failed");
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
