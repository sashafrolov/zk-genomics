use dep::std;
use poseidon::poseidon2::Poseidon2;

// 1. Helper Function: Splits a Field into the {lo, hi} struct required by the library
fn to_curve_scalar(scalar: Field) -> std::embedded_curve_ops::EmbeddedCurveScalar {
    // Split the field into 254 bits (Little Endian)
    let bits = scalar.to_le_bits::<254>();

    // Reconstruct Low 128 bits and High bits
    let mut lo: Field = 0;
    let mut hi: Field = 0;
    let mut two_pow: Field = 1;

    // Sum first 128 bits for Lo
    for i in 0..128 {
        if bits[i] == 1 {
            lo = lo + two_pow;
        }
        two_pow = two_pow * 2;
    }

    // Sum remaining bits for Hi
    two_pow = 1;
    for i in 128..254 {
        if bits[i] == 1 {
            hi = hi + two_pow;
        }
        two_pow = two_pow * 2;
    }

    std::embedded_curve_ops::EmbeddedCurveScalar {
        lo,
        hi
    }
}

// 2. The Verification Logic
pub fn verify_schnorr(
    pub_key_x: Field,
    pub_key_y: Field,
    signature_s: Field,
    signature_e: Field,
    message: Field,
    gen_x: Field,
    gen_y: Field
) {
    let pub_key = std::embedded_curve_ops::EmbeddedCurvePoint {
        x: pub_key_x, y: pub_key_y, is_infinite: false
    };
    let generator = std::embedded_curve_ops::EmbeddedCurvePoint {
        x: gen_x, y: gen_y, is_infinite: false
    };

    let s_scalar = to_curve_scalar(signature_s);

    // FIX: Do not negate e! Use it directly.
    let e_scalar = to_curve_scalar(signature_e);

    // FIX: R = sG + eP (Addition)
    // This matches the Rust formula: s = k - ex
    let points = [generator, pub_key];
    let scalars = [s_scalar, e_scalar];

    let R = std::embedded_curve_ops::multi_scalar_mul(points, scalars);

    // Debug Prints (Optional)
    std::println(R.x);

    // 4. Hash Check
    let e_calculated = Poseidon2:: hash([ R.x,R.y,pub_key_x,pub_key_y,message], 5);

    std::println("--- NOIR CALCULATED R ---");
    println("Rx:");
    std::println(R.x);
    println("Ry:");
    std::println(R.y);
    println(f"pub_key_x is {pub_key_x}");
    println(f"pub_key_y is {pub_key_y}");
    println(f"message is {message}");

    println(f"e_calculated is {e_calculated}");
    println(f"signature_e is {signature_e}");
    assert(e_calculated == signature_e);
}
/*
fn main(
    pub_key_x: Field,
    pub_key_y: Field,
    signature_s: Field,
    signature_e: Field,
    message: Field
) {
    // FIX: Call the function defined above
    verify_schnorr(pub_key_x, pub_key_y, signature_s, signature_e, message);
}
*/