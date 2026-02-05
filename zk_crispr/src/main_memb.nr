//use dep::std;
use poseidon::poseidon2::Poseidon2;
use std::hash::{blake2s, pedersen_hash};

mod on_target_ruleset_one;
mod off_target_mit;
mod membership;
mod schnorr_sig;

fn main(leaves: [Field; membership::INPUT_LEN]) -> pub Field {

    let root = membership::memb_main(leaves);
    println(f"root is {root}");

    root
}