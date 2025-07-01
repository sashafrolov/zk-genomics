


//! Prover inputs for Alignment Circuits

use fxhash::FxHashMap as HashMap;
use crate::ir::term::Value;
use rug::Integer;
use crate::bignat::bignatwithlimbmax::{BigNatWithLimbMax, BigNatbWithLimbMax, BigNatModMultWithLimbMax}; //, BigNatExponWithLimbMax};

use crate::commitment::{Poseidon};


#[cfg(feature = "spartan")]
use crate::right_field_arithmetic::alloc::{map_field, map_field_vec, map_field_double_vec};
#[cfg(feature = "spartan")]
use std::sync::Arc;

#[cfg(feature = "spartan")]
use core::ops::Mul;
use std::path::PathBuf;

use std::time::Instant;
use crate::util::timer::print_time;
use crate::bignat::bignat_adv::BigNatInit;

static BASES_PER_BLOCK : usize = 127;

#[cfg(feature = "spartan")]
/// Prover input for a spartan-curve25519 circuit for basic alignment
/// (Simple cost function and no inclusion proofs)
pub fn prover_input_for_basicalignment(modulus: &Arc<Integer>) -> HashMap<String, Value>{
    let p: usize = 126; // Length (in BP) of the two sequences to be aligned.
    // let mut reference_sequence = vec![vec![0; p]];
    // let mut target_sequence = vec![vec![0; p]; p];
    // let mut cigar_string = vec![vec![0; p]; p];
        let mut matrix = vec![vec![Integer::from(0); p]; p];

    let mut f = vec![Integer::from(1); 4];
    let mut g = vec![Integer::from(1); 4];
    let mut h = vec![Integer::from(1), 
            Integer::from(2), 
            Integer::from(3),
            Integer::from(4), 
            Integer::from(3), 
            Integer::from(2), 
            Integer::from(1)];

    let mut input_map = HashMap::<String, Value>::default();
    map_field_vec(&f, modulus, "f", &mut input_map);
    map_field_vec(&g, modulus, "g", &mut input_map);
    map_field_vec(&h, modulus, "h", &mut input_map);

    input_map
}


#[cfg(feature = "spartan")]
pub fn verifier_input_for_basicalignment(modulus: &Arc<Integer>) -> HashMap<String, Value>{
    let mut input_map = HashMap::<String, Value>::default();

    map_field(&Integer::from(1), modulus, "return", &mut input_map);

    input_map
}