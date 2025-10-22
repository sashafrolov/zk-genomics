//! examples/basic_alignment.rs
//! Spartan version of the alignment circuit previously written
//! in Arkworks. Similar, just hopefully a lot faster.
//!
#[cfg(feature = "jem")]
#[global_allocator]
static GLOBAL: Jemalloc = tikv_jemallocator::Jemalloc;
use neptune::{circuit2::Elt, poseidon::PoseidonConstants, Arity, Strength};
use neptune::sponge::{
    api::{IOPattern, SpongeAPI, SpongeOp},
    circuit::SpongeCircuit,
    vanilla::{Mode, Sponge, SpongeTrait},
};
use bellpepper_core::{
  ConstraintSystem, SynthesisError, LinearCombination,
  boolean::{AllocatedBit, Boolean},
  num::AllocatedNum,
};
use bellpepper::gadgets::boolean::field_into_allocated_bits_le;
use ff::{Field, FromUniformBytes, PrimeField, PrimeFieldBits};
use spartan2::{
  provider::T256HyraxEngine,
  spartan::SpartanSNARK,
  traits::{Engine, circuit::SpartanCircuit, snark::R1CSSNARKTrait},
};
use generic_array::typenum::{U2, U3};
use std::{marker::PhantomData, time::Instant};
use tracing::{info, info_span};
use tracing_subscriber::EnvFilter;

use alignment_circuits::{Base, CigarChar, ToFeltBlocks};
use alignment_circuits::alignment_plain_computation::basic_alignment;

type E = T256HyraxEngine;

const BASES_PER_BLOCK: usize = 125;
const SEQUENCE_BLOCK_LENGTH: usize = 1 << 4;
const SEQUENCE_BASE_PAIRS: usize = SEQUENCE_BLOCK_LENGTH * BASES_PER_BLOCK;
const CIGAR_STRING_LENGTH: usize = SEQUENCE_BASE_PAIRS;
const CIGAR_STRING_LENGTH_BLOCKS: usize = SEQUENCE_BASE_PAIRS.div_ceil(BASES_PER_BLOCK);

#[derive(Clone, Debug)]
struct BasicAlignmentCircuit<Scalar: PrimeField> {
  pub reference_sequence_felts: Vec<Scalar>, // The reference for a certain gene, encoded as field elements, where BASES_PER_BLOCK bases are packed per field element
  pub reference_sequence_bases: Vec<Base>, // Reference sequence
  pub target_sequence_felts: Vec<Scalar>, // The value being aligned against the target
  pub target_sequence_bases: Vec<Base>,
  pub cigar_string_felts: Vec<Scalar>, 
  pub cigar_string_chars: Vec<CigarChar>,
  pub alignment_score: usize, // claimed alignment score which is a public output. 0 is perfect, +1 for each insertion or deletion in the basic version.
  
  _p: PhantomData<Scalar>,
}

impl<Scalar: PrimeField + PrimeFieldBits> BasicAlignmentCircuit<Scalar> {
  fn new(reference_sequence_bases: Vec<Base>, target_sequence_bases: Vec<Base>) -> Self {
    let reference_sequence_felts = reference_sequence_bases.to_felt_blocks::<Scalar>(BASES_PER_BLOCK);
    let target_sequence_felts = target_sequence_bases.to_felt_blocks::<Scalar>(BASES_PER_BLOCK);

    let (cigar_string_chars, alignment_score) = basic_alignment(reference_sequence_bases.clone(), target_sequence_bases.clone(), 0.0, -1.0, -1.0);
    let cigar_string_felts = cigar_string_chars.to_felt_blocks(BASES_PER_BLOCK);

    Self {
      reference_sequence_felts,
      reference_sequence_bases,
      target_sequence_felts,
      target_sequence_bases,
      cigar_string_felts,
      cigar_string_chars,
      alignment_score,
      _p: PhantomData,
    }
  }
}

impl<E: Engine> SpartanCircuit<E> for BasicAlignmentCircuit<E::Scalar> {
  fn public_values(&self) -> Result<Vec<<E as Engine>::Scalar>, SynthesisError> {
    // let default_poseidon_params = Sponge::<<E as Engine>::Scalar, U2>::api_constants(Strength::Standard);
    // let parameter = IOPattern(vec![
    //     SpongeOp::Absorb(self.preimage.len() as u32),
    //     SpongeOp::Squeeze(1),
    // ]);
    // let mut sponge = Sponge::<<E as Engine>::Scalar, U2>::new_with_constants(&default_poseidon_params, Mode::Simplex);
    // let acc = &mut ();

    // sponge.start(parameter, None, acc);
    // SpongeAPI::absorb(&mut sponge, self.preimage.len() as u32, &self.preimage, acc);

    // let output = SpongeAPI::squeeze(&mut sponge, 1, acc);
    // assert_eq!(output.len(), 1);

    // sponge.finish(acc).unwrap();
    let mut public_values = Vec::new();

    for block in &self.reference_sequence_felts {
        public_values.push(block.clone());
    }

    let public_score = <E as Engine>::Scalar::from_u128(self.alignment_score as u128);
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
    let target_sequence_input_vars = self.target_sequence_felts.clone()
      .into_iter()
      .enumerate()
      .map(|(i, block)| 
          AllocatedNum::alloc(cs.namespace(|| format!("Target sequence block {i}")), || Ok(block))
      )
      .collect::<Result<Vec<_>, _>>()?;

    let target_sequence_base_vars = self.target_sequence_bases.clone()
      .into_iter()
      .enumerate()
      .map(|(i, base)| 
          AllocatedNum::alloc(cs.namespace(|| format!("Target sequence base {i}")), || Ok(base.to_field()))
      )
      .collect::<Result<Vec<_>, _>>()?;

    // This approach does embed the length of the cigar string into the circuit, with a little more work you could
    // "pad" the CIGAR string to not leak this info.
    let cigar_string_input_vars = self.cigar_string_felts.clone()
      .into_iter()
      .enumerate()
      .map(|(i, block)| 
          AllocatedNum::alloc(cs.namespace(|| format!("Cigar string character block {i}")), || Ok(block))
      )
      .collect::<Result<Vec<_>, _>>()?;

    let cigar_string_char_vars = self.cigar_string_chars.clone()
      .into_iter()
      .enumerate()
      .map(|(i, char)| 
          AllocatedNum::alloc(cs.namespace(|| format!("Cigar string character {i}")), || Ok(char.to_field()))
      )
      .collect::<Result<Vec<_>, _>>()?;

    // These are public because this is the reference.
    let reference_sequence_input_vars = self.reference_sequence_felts.clone()
      .into_iter()
      .enumerate()
      .map(|(i, block)| 
          AllocatedNum::alloc_input(cs.namespace(|| format!("Reference sequence block {i}")), || Ok(block))
      )
      .collect::<Result<Vec<_>, _>>()?;

    let reference_sequence_base_vars = self.reference_sequence_bases.clone()
      .into_iter()
      .enumerate()
      .map(|(i, base)| 
          AllocatedNum::alloc(cs.namespace(|| format!("Reference sequence base {i}")), || Ok(base.to_field()))
      )
      .collect::<Result<Vec<_>, _>>()?;

    // The score needs to be public as well.
    let alignment_score_public = AllocatedNum::alloc_input(cs.namespace(|| "public alignment score"), || Ok(E::Scalar::from_u128(self.alignment_score as u128)))?;

    // 2. Enforce that the bases are correct (this is kind of shitty in Bellpepper unfortunately):
    // TODO: Factor out a function here.
    let TWO = E::Scalar::from(2u64);
    for (i, block) in target_sequence_input_vars.iter().enumerate() {
        let block_as_bits = field_into_allocated_bits_le(cs.namespace(|| format!("Target sequence felt block {i} decomposition")), Some(self.target_sequence_felts[i]))?;
        for j in (0..BASES_PER_BLOCK) {
            cs.enforce(|| format!("Enforcing base decomposition for target sequence block {i} base {j}"), 
                |lc| lc + CS::one(), 
                |lc| lc + (TWO, block_as_bits[2*j + 1].get_variable()) + block_as_bits[2*j].get_variable(), 
                |lc| lc + target_sequence_base_vars[i * BASES_PER_BLOCK + j].get_variable());
        }
        let mut pow_of_two = E::Scalar::ONE;
        let mut overall_decomposition_lc = LinearCombination::zero();
        for bit in block_as_bits {
            overall_decomposition_lc = overall_decomposition_lc + (pow_of_two, bit.get_variable());
            pow_of_two = pow_of_two * TWO;
        }

        cs.enforce(|| format!("Enforcing overall bit decomposition for target sequence block {i}"), 
            |lc| lc + CS::one(),
            |lc| lc + &overall_decomposition_lc, 
            |lc| lc + block.get_variable(),
        );
    }

    for (i, block) in reference_sequence_input_vars.into_iter().enumerate() {
        let block_as_bits = field_into_allocated_bits_le(cs.namespace(|| format!("Reference sequence felt block {i} decomposition")), Some(self.reference_sequence_felts[i]))?;
        for j in (0..BASES_PER_BLOCK) {
            cs.enforce(|| format!("Enforcing base decomposition for reference sequence block {i} base {j}"), 
                |lc| lc + CS::one(), 
                |lc| lc + (TWO, block_as_bits[2*j + 1].get_variable()) + block_as_bits[2*j].get_variable(), 
                |lc| lc + reference_sequence_base_vars[i * BASES_PER_BLOCK + j].get_variable());
        }
        let mut pow_of_two = E::Scalar::ONE;
        let mut overall_decomposition_lc = LinearCombination::zero();
        for bit in block_as_bits {
            overall_decomposition_lc = overall_decomposition_lc + (pow_of_two, bit.get_variable());
            pow_of_two = pow_of_two * TWO;
        }

        cs.enforce(|| format!("Enforcing overall bit decomposition for reference sequence block {i}"), 
            |lc| lc + CS::one(),
            |lc| lc + &overall_decomposition_lc, 
            |lc| lc + block.get_variable(),
        );
    }

    for (i, block) in cigar_string_input_vars.iter().enumerate() {
        let block_as_bits = field_into_allocated_bits_le(cs.namespace(|| format!("Cigar string felt block {i} decomposition")), Some(self.cigar_string_felts[i]))?;
        for j in (0..BASES_PER_BLOCK) {
            cs.enforce(|| format!("Enforcing base decomposition for cigar string block {i} char {j}"), 
                |lc| lc + CS::one(), 
                |lc| lc + (TWO, block_as_bits[2*j + 1].get_variable()) + block_as_bits[2*j].get_variable(), 
                |lc| lc + cigar_string_char_vars[i * BASES_PER_BLOCK + j].get_variable());
        }
        let mut pow_of_two = E::Scalar::ONE;
        let mut overall_decomposition_lc = LinearCombination::zero();
        for bit in block_as_bits {
            overall_decomposition_lc = overall_decomposition_lc + (pow_of_two, bit.get_variable());
            pow_of_two = pow_of_two * TWO;
        }

        cs.enforce(|| format!("Enforcing overall bit decomposition for cigar string block {i}"), 
            |lc| lc + CS::one(),
            |lc| lc + &overall_decomposition_lc, 
            |lc| lc + block.get_variable(),
        );
    }

    // 3. Compute a hash for random challenges (will remove this part later in favor of random challenges.)
    let (memcheck_challenge_0, memcheck_challenge_1) = {
      let default_poseidon_params = Sponge::<<E as Engine>::Scalar, U2>::api_constants(Strength::Standard);
      let mut sponge = SpongeCircuit::<<E as Engine>::Scalar, U2, _>::new_with_constants(&default_poseidon_params, Mode::Simplex);

      let poseidon_hash_input_len = self.target_sequence_felts.len() + self.cigar_string_felts.len();
      let parameter = IOPattern(vec![
          SpongeOp::Absorb(poseidon_hash_input_len as u32),
          SpongeOp::Squeeze(2),
      ]);

      let ns = &mut cs.namespace(|| "Poseidon Sponge Start");

      sponge.start(parameter, None, ns);

      let preimage_felts_reallocated: Vec<Elt<<E as Engine>::Scalar>> = target_sequence_input_vars
        .into_iter()
        .chain(cigar_string_input_vars.into_iter())
        .map(|s| Elt::Allocated(s))
        .collect();

      SpongeAPI::absorb(&mut sponge, poseidon_hash_input_len as u32, preimage_felts_reallocated.as_slice(), ns);

      let calc_node = SpongeAPI::squeeze(&mut sponge, 2, ns);

      assert_eq!(calc_node.len(), 2);

      sponge.finish(ns).unwrap();

      let chall_0 = calc_node[0].ensure_allocated(&mut ns.namespace(|| "Challenge 0"), true)?;
      let chall_1 = calc_node[1].ensure_allocated(&mut ns.namespace(|| "Challenge 1"), true)?;
      (chall_0, chall_1)
    };

    // 4. Verify alignment: 

    // Initialize LHS of memcheck products
    // TODO: Update the memcheck computation to include indices with random linear combination.
    let mut target_sequence_memcheck_product_left = AllocatedNum::alloc(cs.namespace(|| "Initial target sequence left memcheck product"), || Ok(E::Scalar::ONE))?;
    for (i, base) in target_sequence_base_vars.iter().enumerate() {
      let addition = base.add(cs.namespace(|| format!("Left target memcheck product addition {i}")), &memcheck_challenge_0)?;
      target_sequence_memcheck_product_left = target_sequence_memcheck_product_left.mul(cs.namespace(|| format!("Left target memcheck product multiplication {i}")), &addition)?;
    }
    
    let mut reference_sequence_memcheck_product_left = AllocatedNum::alloc(cs.namespace(|| "Initial reference sequence left memcheck product"), || Ok(E::Scalar::ONE))?;
    for (i, base) in reference_sequence_base_vars.iter().enumerate() {
      let addition = base.add(cs.namespace(|| format!("Left reference memcheck product addition {i}")), &memcheck_challenge_0)?;
      reference_sequence_memcheck_product_left = reference_sequence_memcheck_product_left.mul(cs.namespace(|| format!("Left reference memcheck product multiplication {i}")), &addition)?;
    }
    
    // Constants
    let ALIGNMENT_MATCH = AllocatedNum::alloc(cs.namespace(|| "match constant"), || Ok(E::Scalar::ZERO))?;
    let INSERTION = AllocatedNum::alloc(cs.namespace(|| "insertion constant"), || Ok(E::Scalar::ONE))?;
    let DELETION = AllocatedNum::alloc(cs.namespace(|| "deletion constant"), || Ok(E::Scalar::from_u128(2u128)))?;

    // Initialize variables that get updated in the loop
    let mut target_index_var = AllocatedNum::alloc(cs.namespace(|| "Initial index into target string"), || Ok(E::Scalar::ZERO))?;
    let mut reference_index_var = AllocatedNum::alloc(cs.namespace(|| "Initial index into reference string"), || Ok(E::Scalar::ZERO))?;
    let mut target_index = 0usize;
    let mut reference_index = 0usize;
    let mut target_sequence_memcheck_product_right = AllocatedNum::alloc(cs.namespace(|| "Initial target sequence right memcheck product"), || Ok(E::Scalar::ONE))?;
    let mut reference_sequence_memcheck_product_right = AllocatedNum::alloc(cs.namespace(|| "Initial reference sequence right memcheck product"), || Ok(E::Scalar::ONE))?;
    let mut alignment_score = AllocatedNum::alloc(cs.namespace(|| "Initial alignment score quantity"), || Ok(E::Scalar::ZERO))?;
    for (i, char) in cigar_string_char_vars.iter().enumerate() {
      // Booleans corresponding to each possible CIGAR string character
      let is_match = AllocatedNum::alloc(cs.namespace(|| format!("is_match comparison operator {i}")), || Ok(if self.cigar_string_chars[i] == CigarChar::Match {E::Scalar::ONE} else {E::Scalar::ZERO}))?;
      cs.enforce(|| format!("is_match equality constraint {i}"), 
        |lc| lc + char.get_variable(), // Char will be zero when equality passes. 
        |lc| lc + is_match.get_variable(), 
        |_| LinearCombination::zero());
      cs.enforce(|| format!("is_match booleanity constraint {i}"), 
        |lc| lc + is_match.get_variable(),
        |lc| lc + CS::one() - is_match.get_variable(), 
        |_| LinearCombination::zero());

      let is_insertion = AllocatedNum::alloc(cs.namespace(|| format!("is_insertion comparison operator {i}")), || Ok(if self.cigar_string_chars[i] == CigarChar::Insert {E::Scalar::ONE} else {E::Scalar::ZERO}))?;
      cs.enforce(|| format!("is_insertion equality constraint {i}"), 
        |lc| lc + char.get_variable() - CS::one(), // Char will be one when equality passes. 
        |lc| lc + is_insertion.get_variable(), 
        |_| LinearCombination::zero());
      cs.enforce(|| format!("is_insertion booleanity constraint {i}"), 
        |lc| lc + is_insertion.get_variable(), 
        |lc| lc + CS::one() - is_insertion.get_variable(), 
        |_| LinearCombination::zero());

      let is_deletion = AllocatedNum::alloc(cs.namespace(|| format!("is_deletion comparison operator {i}")), || Ok(if self.cigar_string_chars[i] == CigarChar::Delete {E::Scalar::ONE} else {E::Scalar::ZERO}))?;
      cs.enforce(|| format!("is_deletion equality constraint {i}"), 
        |lc| lc + char.get_variable() - CS::one() - CS::one(), // Char will be two when equality passes. 
        |lc| lc + is_deletion.get_variable(), 
        |_| LinearCombination::zero());
      cs.enforce(|| format!("is_deletion booleanity constraint {i}"), 
        |lc| lc + is_deletion.get_variable(), 
        |lc| lc + CS::one() - is_deletion.get_variable(), 
        |_| LinearCombination::zero());

      // Update scoring function (basic alignment scoring rn):
      alignment_score = alignment_score.add(cs.namespace(|| format!("Alignment char {i} score first addition")), &is_insertion)?;
      alignment_score = alignment_score.add(cs.namespace(|| format!("Alignment char {i} score second addition")), &is_deletion)?;

      // Take as advice the values that we read from the sequence at various indices.
      let target_sequence_read_val = AllocatedNum::alloc(cs.namespace(|| format!("Reading value from target sequence for cigar char {i}")), || Ok(self.target_sequence_bases[target_index].to_field()))?;
      let reference_sequence_read_val = AllocatedNum::alloc(cs.namespace(|| format!("Reading value from reference sequence for cigar char {i}")), || Ok(self.reference_sequence_bases[reference_index].to_field()))?;

      // Update the memcheck product with the read values.
      // TODO: Factor in the read index for security.
      
      // target_sequence_memcheck_product_right *= (&is_match | &is_insertion).select(&(&challenge_vars[0] + &target_sequence_read_val + &target_index_var * &challenge_vars[1]), &FpVar::new_constant(cs.clone(), F::one()).unwrap()).unwrap();
      
      let is_target_sequence_read_from = (self.cigar_string_chars[i] == CigarChar::Match) || (self.cigar_string_chars[i] == CigarChar::Insert); 
      let target_memcheck_addition_1 = target_sequence_read_val.add(cs.namespace(|| format!("Right target memcheck product addition {i}")), &memcheck_challenge_0)?;
      // Add the conditional
      target_sequence_memcheck_product_right = target_sequence_memcheck_product_right.mul(cs.namespace(|| format!("Right target memcheck product multiplication {i}")), &target_memcheck_addition_1)?;
      
      reference_sequence_memcheck_product_right *= (&is_match | &is_deletion).select(&(&challenge_vars[0] + &reference_sequence_read_val + &reference_index_var * &challenge_vars[1]), &FpVar::new_constant(cs.clone(), F::one()).unwrap()).unwrap();

      // Assert that, if the CIGAR string says that characters match, then there is an actual match.
      // Equality check.
      let do_bases_match = AllocatedNum::alloc(cs.namespace(|| format!("Base equality check for cigar char {i}")), || Ok(if self.target_sequence_bases[target_index] == self.reference_sequence_bases[reference_index] {E::Scalar::ONE} else {E::Scalar::ZERO}))?;
      cs.enforce(|| format!("base equality check {i} equality constraint"), 
        |lc| lc + target_sequence_read_val.get_variable() - reference_sequence_read_val.get_variable(),
        |lc| lc + do_bases_match.get_variable(), 
        |_| LinearCombination::zero());
      cs.enforce(|| format!("base equality check {i} booleanity constraint"), 
        |lc| lc + do_bases_match.get_variable(), 
        |lc| lc + CS::one() - do_bases_match.get_variable(), 
        |_| LinearCombination::zero());
      // Actual enforcement check. Assert that (!is_match) | bases_match is true.
      cs.enforce(|| format!("Conditional match check for CIGAR char {i}"), 
        |lc| lc + is_match.get_variable(), 
        |lc| lc + CS::one() - do_bases_match.get_variable(), 
        |_| LinearCombination::zero());

      // These 3 blocks update the next index to read from in regular computation + the circuit.
      target_index_var = target_index_var.add(cs.namespace(|| format!("Alignment char {i} target index update first addition")), &is_match)?;
      target_index_var = target_index_var.add(cs.namespace(|| format!("Alignment char {i} target index update second addition")), &is_insertion)?;
      
      reference_index_var = reference_index_var.add(cs.namespace(|| format!("Alignment char {i} reference index update first addition")), &is_match)?;
      reference_index_var = reference_index_var.add(cs.namespace(|| format!("Alignment char {i} reference index update second addition")), &is_deletion)?;
      
      match self.cigar_string_chars[i] {
          CigarChar::Match => {target_index+=1; reference_index +=1},
          CigarChar::Insert => {target_index+=1;},
          CigarChar::Delete => {reference_index +=1},
          _ => {panic!("Witness generation reached an incorrect CIGAR character")}
      }
    }

    // Enforce that the memcheck products are equal.
    cs.enforce(|| format!("Check that the target string memcheck products match"), 
      |lc| lc + target_sequence_memcheck_product_left.get_variable() - target_sequence_memcheck_product_right.get_variable(), 
      |lc| lc + CS::one(), 
      |_| LinearCombination::zero());
    cs.enforce(|| format!("Check that the reference string memcheck products match"), 
      |lc| lc + reference_sequence_memcheck_product_left.get_variable() - reference_sequence_memcheck_product_right.get_variable(), 
      |lc| lc + CS::one(), 
      |_| LinearCombination::zero());

    // Enforce that the public alignment score matches what was computed by the circuit.
    cs.enforce(|| format!("Check that alignment score matches public output"), 
      |lc| lc + alignment_score_public.get_variable() - alignment_score.get_variable(), 
      |lc| lc + CS::one(), 
      |_| LinearCombination::zero());

    Ok(vec![])
  }

  fn num_challenges(&self) -> usize {
    // SHA-256 circuit does not expect any challenges
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
    .with_ansi(true)                // no bold colour codes
    .with_env_filter(EnvFilter::from_default_env())
    .init();

  let reference_sequence_bases = Base::random_sequence(SEQUENCE_BASE_PAIRS);
  let target_sequence_bases = reference_sequence_bases.clone();

  let circuit = BasicAlignmentCircuit::<<E as Engine>::Scalar>::new(reference_sequence_bases, target_sequence_bases);

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

    // Summary
  info!(
      "SUMMARY cigar={} bases, setup={} ms, prep_prove={} ms, prove={} ms, verify={} ms",
      cigar_len, setup_ms, prep_ms, prove_ms, verify_ms
  );
  drop(root_span);

}
