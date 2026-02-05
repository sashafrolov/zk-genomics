
global SCALE: Field = 1048576; // 2^20
global SCALE_POW2: u32 = 20; // 2^20

// mit weights (1-mit.weights[index])*2^20
global MIT_WEIGHTS_VALUES: [Field; 20] = [1048576, 1048576, 1033895, 1048576, 1048576, 634388, 716177, 1048576, 640679, 965738, 581959, 515899, 405798, 156237, 281018, 180355, 403701, 205520, 330301, 437256];

// 1/m^2 *2^20
global T2_VALUES: [Field; 20] = [1048576, 262144, 116508, 65536, 41943, 29127, 21399, 16384, 12945, 10485, 8665, 7281, 6204, 5349, 4660, 4096, 3628, 3236, 2904, 2621];

// PAM scores *2^20
global PAM_VALUES: [Field; 16] = [0, 0, 271853, 0, 0, 0, 112347, 0, 72817, 23301, 1048576, 16912, 0, 0, 40853, 0];

global HIGH_THRESHOLD: u64 = 838860;
global MEDIUM_THRESHOLD: u64 = 629145;
global LOW_THRESHOLD: u64 = 524288;

/////////////////////////////
//unsafe {print_value(result as Field)}
unconstrained fn print_value(x:  Field) {
    let mut x_u64 = x as u64;
    let print_scale = 1000000;
    x_u64 = x_u64 * print_scale;
    x_u64 = (x_u64 - (x_u64%(SCALE as u64)))/(SCALE as u64);
    print(f"{x_u64}/{print_scale}");
}

// For Field right shift: use unconstrained hint pattern
unconstrained fn shr_hint<let N:u32>(x:  Field) -> (Field, Field) {
let divisor:  u64 = 1 << (N as u64);
let x_val = x as u64;
((x_val / divisor) as Field, (x_val % divisor) as Field)
}

fn field_shr<let N: u32>(x: Field) -> Field {
let divisor: Field = (1 << N) as Field;
let (quotient, remainder) = unsafe { shr_hint::<N>(x) };

// Verify:  x == quotient * 2^N + remainder
assert(x == quotient * divisor + remainder);
remainder.assert_max_bit_size::<N>();  // remainder < 2^N

quotient
}

// Unconstrained hint for division
unconstrained fn div_hint(numerator: Field, divisor: Field) -> (Field, Field) {
    let num = numerator as u64;
    let div = divisor as u64;
    let quotient = num / div;
    let remainder = num % div;
    (quotient as Field, remainder as Field)
}

// Prove a < b using the hint pattern
unconstrained fn lt_hint(a: Field, b: Field) -> Field {
    // Returns b - a - 1, which should be >= 0 if a < b
    let a_val = a as u64;
    let b_val = b as u64;
    (b_val - a_val - 1) as Field
}


fn assert_lt<let BITS:u32>(a: Field, b: Field) {
// Prove a < b by showing (b - a - 1) is a valid non-negative number
let diff = unsafe { lt_hint(a, b) };
assert(a + diff + 1 == b);
diff. assert_max_bit_size::<BITS>();
}

///////////////////////////////////////

fn multiply_fixed_mitweights(a: Field, b: Field) -> Field {
    field_shr::<SCALE_POW2>(a*b)
}


fn get_avg_distance(min_index: Field, max_index:Field, mismatches:Field) -> Field {
    /*
        let mod_input = ((max_index-min_index)*SCALE) as u64;
        let remainder = mod_input % (((mismatches-1)) as u64);
        ((max_index-min_index)*SCALE - (remainder as Field))/(mismatches-1)
     */
    let numerator = (max_index - min_index) * SCALE;
    let divisor = mismatches - 1;

    // Get quotient and remainder via unconstrained hint
    let (quotient, remainder) = unsafe { div_hint(numerator, divisor) };

    // Constrain:  numerator == quotient * divisor + remainder
    assert(numerator == quotient * divisor + remainder);

    // Constrain: remainder < divisor
    // Since mismatches is 0-21, divisor is at most 20, so remainder < 20
    // 5 bits can represent 0-31, which covers 0-19
    remainder.assert_max_bit_size::<5>();

    // Additional safety: verify remainder < divisor explicitly
    // This is needed because assert_max_bit_size only proves remainder < 32
    assert((remainder as u8) < (divisor as u8));

    quotient
}

// TODO: can this be improved in anyway?
fn get_t3(min_index: Field, max_index:Field, mismatches:Field) -> Field {
    let numerator_scaled = 19 * (mismatches - 1) * SCALE;
    let denominator = 95 * (mismatches - 1) - 4 * (max_index - min_index);

    let remainder = (numerator_scaled as u64) % (denominator as u64);
    (numerator_scaled - (remainder as Field)) / denominator
}

pub fn off_target_mit_score(spacer: [Field; 20], protospacer: [Field; 20], pam: [Field; 3]) -> [Field; 3] {
    let mut mismatches:u64 = 0;
    let mut min_index:u64 = 20;
    let mut max_index:u64 = 0;

    let mut t1: Field = SCALE;
    for i in 0..20 {
        if spacer[i] != protospacer[i] {
            mismatches += 1;
            //println(f"i is {i}");
            t1 = multiply_fixed_mitweights(t1, MIT_WEIGHTS_VALUES[i]);

            let iu64 = i as u64;
            if iu64 < min_index {
                min_index = iu64;
            }

            if iu64 > max_index {
                max_index = iu64;
            }
        }
    }
    //println(f"The mismatches is {mismatches}");
    let mut score = SCALE;

    let no_mismatches: bool = (mismatches == 0);
    //println(f"The no_mismatches is {no_mismatches}");
    if !no_mismatches {
        //println(f"The t1 is {t1}");
        //unsafe {print_value(t1)}
        //println("");

        score = t1;
        if mismatches > 0 {
            score = multiply_fixed_mitweights(t1, T2_VALUES[mismatches as u32 -1]);
        }

        //println(f"The t1_t2 is {score}");
        //unsafe {print_value(score)}
        //println("");
        //println(f"The min_index is {min_index}");
        //println(f"The max_index is {max_index}");

        let mut t3:Field = SCALE;
        let min_index_f = min_index as Field;
        let max_index_f = max_index as Field;
        let mismatches_f = mismatches as Field;
        let mut d = 19;
        if mismatches > 1 {
            d = get_avg_distance(min_index_f, max_index_f, mismatches_f);
            t3 = get_t3(min_index_f, max_index_f, mismatches_f);
        }
        //println(f"The t3 is {t3}");
        //unsafe {print_value(t3)}
        //println("");
        //println(f"The d is {d}");

        score = multiply_fixed_mitweights(score, t3);
        //println(f"The t1_t2_t3 is {score}");
        //unsafe {print_value(score)}
        //println("");
    }
    //println(f"The score is {score}");
    let pam_index = (4*pam[1] + pam[2]) as u32;
    //println(f"The pam_index is {pam_index}");
    let pam_value = PAM_VALUES[pam_index];
    //println(f"The pam_value is {pam_value}");
    score = multiply_fixed_mitweights(score, PAM_VALUES[pam_index]);

    let score_u64 = score as u64;
    //println(f"The score is {score_u64}");
    //unsafe {print_value(score)}
    //println("");

    let score_u64 = score as u64;
    let mut out_arr: [Field; 3] = [0;3];
    if score_u64 > HIGH_THRESHOLD {
        //println("High Chance");
        out_arr[0] = 1;
    } else if score_u64 > MEDIUM_THRESHOLD {
        //println("Medium Chance");
        out_arr[1] = 1;
    } else {
        //println("Low Chance");
        out_arr[2] = 1;
    }
    out_arr
}