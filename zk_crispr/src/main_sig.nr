//use dep::std;
use poseidon::poseidon2::Poseidon2;
use std::hash::{blake2s, pedersen_hash};

mod on_target_ruleset_one;
mod off_target_mit;
mod membership;
mod schnorr_sig;

fn main( signature_s: Field, signature_e: Field, message: Field) -> pub Field {
    let gen_x: Field = 0x0000000000000000000000000000000000000000000000000000000000000001;
    let gen_y: Field = 0x0000000000000002cf135e7506a45d632d270d45f1181294833fc48d823f272c;
    let pub_key_x: Field     = 0x2a42d6bee20e865f9646d818ca977390a1bad12b60db174f216d66f266086bec;
    let pub_key_y: Field      = 0x14eac26c8b7a5241c580aac438dada4b8978a7e2e9bfce55004d9689d9c892cd;
    //let signature_s: Field    = 0x25947dda8d4743312ea2914a4952547ac97ae6cf6c309992559a538e0f85b3c8;
    //let signature_e: Field    = 0x22405a5fd116fddb51a739531fb37d8819996aca97925f22bcbf7c9c021f7f7a;
    //let message: Field        = 0x0000000000000000000000000000000000000000000000000000000000000539;

    schnorr_sig::verify_schnorr(
        pub_key_x,
        pub_key_y,
        signature_s,
        signature_e,
        message,
        gen_x,
        gen_y,
    );

    message


}