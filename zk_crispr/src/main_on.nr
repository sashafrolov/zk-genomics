//use dep::std;
use poseidon::poseidon2::Poseidon2;
use std::hash::{blake2s, pedersen_hash};

mod on_target_ruleset_one;
mod off_target_mit;
mod membership;
mod schnorr_sig;

fn main(leaves: [Field; membership::INPUT_LEN]) -> pub [Field; 4] {

    let mut on_target_output: [Field; 4] = [0; 4];

    // hard coded into the circuit
    let mut seq = [0; 30];
    for j in 0..membership::INPUT_LEN-30 {
        for i in 0..30 {
            seq[i] = leaves[i+j];
        }

        let on_targ_arr = on_target_ruleset_one::on_target_ruleset_one_score(seq);


        for i in 0..4 {
            on_target_output[i] = on_target_output[i] + on_targ_arr[i];
        }
    }

    // now doign the reverse complement
    let mut reverse_compl_leaves = [0; membership::INPUT_LEN];
    for i in 0..membership::INPUT_LEN {
        reverse_compl_leaves[i] = 3 - leaves[membership::INPUT_LEN - 1 - i];
    }

    for j in 0..membership::INPUT_LEN-30 {
        for i in 0..30 {
            seq[i] = reverse_compl_leaves[i+j];
        }

        let on_targ_arr = on_target_ruleset_one::on_target_ruleset_one_score(seq);


        for i in 0..4 {
            on_target_output[i] = on_target_output[i] + on_targ_arr[i];
        }
    }

    std::println(f"on_target_output Array: {on_target_output}");
    on_target_output
}