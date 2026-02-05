//use dep::std;
use poseidon::poseidon2::Poseidon2;
use std::hash::{blake2s, pedersen_hash};

mod on_target_ruleset_one;
mod off_target_mit;
mod membership;
mod schnorr_sig;

fn main(leaves: [Field; membership::INPUT_LEN]) -> pub [Field; 3] {

    let mut off_target_output: [Field; 3] = [0; 3];

    // hard coded into the circuit
    let  spacer: [Field; 20] = [3, 2, 0, 0, 3, 2, 1, 0, 3, 2, 1, 0, 3,2, 3, 0, 3, 0, 2, 2];
    let mut protospacer = [0; 20];
    let mut pam = [0; 3];

    for j in 0..membership::INPUT_LEN-23 {

        for i in 0..20 {
            protospacer[i] = leaves[i+j];
        }

        for i in 0..3 {
            pam[i] = leaves[i+j+20];
        }
        let off_targ_arr = off_target_mit::off_target_mit_score(spacer, protospacer, pam);


        for i in 0..3 {
            off_target_output[i] = off_target_output[i] + off_targ_arr[i];
        }
    }

    // now doign the reverse complement
    let mut reverse_compl_leaves = [0; membership::INPUT_LEN];
    for i in 0..membership::INPUT_LEN {
        reverse_compl_leaves[i] = 3 - leaves[membership::INPUT_LEN - 1 - i];
    }

    for j in 0..membership::INPUT_LEN-23 {
        for i in 0..20 {
            protospacer[i] = reverse_compl_leaves[i+j];
        }

        for i in 0..3 {
            pam[i] = reverse_compl_leaves[i+j+20];
        }
        let off_targ_arr = off_target_mit::off_target_mit_score(spacer, protospacer, pam);


        for i in 0..3 {
            off_target_output[i] = off_target_output[i] + off_targ_arr[i];
        }
    }

    std::println(f"off_target_output Array: {off_target_output}");
    off_target_output
}