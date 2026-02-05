//use dep::std;
use poseidon::poseidon2::Poseidon2;
use std::hash::{blake2s, pedersen_hash};

mod on_target_ruleset_one;
mod off_target_mit;
mod membership;
mod schnorr_sig;

fn main(seq_chunk: [Field; membership::INPUT_LEN]) -> pub ( [Field; 4], [Field; 3]) {
    let on_target_start_index: u32 = 1000;
    let on_target_end_index: u32 = 3000;

    let mut on_target_output: [Field; 4] = [0; 4];
    let mut off_target_output: [Field; 3] = [0; 3];

    let mut on_targ_seq = [0; 30];

    // hard coded into the circuit
    let  spacer: [Field; 20] = [3, 2, 0, 0, 3, 2, 1, 0, 3, 2, 1, 0, 3,2, 3, 0, 3, 0, 2, 2];
    let mut protospacer = [0; 20];
    let mut pam = [0; 3];

    for j in 0..membership::INPUT_LEN-23 {
        if (j  >= on_target_start_index) & (j < on_target_end_index)  & (j+30) <= membership::INPUT_LEN {
            for i in 0..30 {
                on_targ_seq[i] = seq_chunk[i+j];
            }

            let on_targ_arr = on_target_ruleset_one::on_target_ruleset_one_score(on_targ_seq);

            for i in 0..4 {
                on_target_output[i] = on_target_output[i] + on_targ_arr[i];
            }

        } else {
            for i in 0..20 {
                protospacer[i] = seq_chunk[i+j];
            }

            for i in 0..3 {
                pam[i] = seq_chunk[i+j+20];
            }
            let off_targ_arr = off_target_mit::off_target_mit_score(spacer, protospacer, pam);


            for i in 0..3 {
                off_target_output[i] = off_target_output[i] + off_targ_arr[i];
            }
        }
    }

    // now doign the reverse complement
    let mut reverse_seq_chunk = [0; membership::INPUT_LEN];
    for i in 0..membership::INPUT_LEN {
        reverse_seq_chunk[i] = 3 - seq_chunk[membership::INPUT_LEN - 1 - i];
    }

    let reverse_on_target_start_index = membership::INPUT_LEN - on_target_end_index;
    let reverse_on_target_end_index = membership::INPUT_LEN - on_target_start_index;
    for j in 0..membership::INPUT_LEN-23 {
        if (j  >= reverse_on_target_start_index) & (j < reverse_on_target_end_index)  & (j+30) <= membership::INPUT_LEN {
            for i in 0..30 {
                on_targ_seq[i] = reverse_seq_chunk[i+j];
            }

            let on_targ_arr = on_target_ruleset_one::on_target_ruleset_one_score(on_targ_seq);

            for i in 0..4 {
                on_target_output[i] = on_target_output[i] + on_targ_arr[i];
            }

        } else {
            for i in 0..20 {
                protospacer[i] = reverse_seq_chunk[i+j];
            }

            for i in 0..3 {
                pam[i] = reverse_seq_chunk[i+j+20];
            }
            let off_targ_arr = off_target_mit::off_target_mit_score(spacer, protospacer, pam);


            for i in 0..3 {
                off_target_output[i] = off_target_output[i] + off_targ_arr[i];
            }
        }
    }

    std::println(f"on_target_output Array: {on_target_output}");
    (on_target_output, off_target_output)
}