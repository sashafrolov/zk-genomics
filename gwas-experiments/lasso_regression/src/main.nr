global EVAL_SET_SIZE: u32 = 100;
global NUM_FEATURES: u32 = 999; // This is not sparse, may change later.
global NUM_COEFFS: u32 = NUM_FEATURES + 1; // There is an additional bias term.
global FIXED_POINT_PRECISION_BYTES: u32 = 4; 
global FIXED_POINT_MAX_MAGNITUDE_BYTES: u32 = 4; // Implicit precision assumption that these two precisions add to less than 15, since u128's are used in here.
global RIGHT_SHIFT_FACTOR : Field = 2.pow_32((FIXED_POINT_PRECISION_BYTES * 8) as Field);
global FIXED_POINT_ZERO : Field = 2.pow_32((FIXED_POINT_PRECISION_BYTES * 8 + FIXED_POINT_MAX_MAGNITUDE_BYTES * 8) as Field);

// X is the set of data points in the evaluation set.
// y is the set of expected outputs for the evaluation set.
// beta is the set of claimed coefficients, which is public. (note that the bias term is the last rather than the first.)
// regularization_constraint is the value that the L1 norm of beta must be less than.
// All of these values must be in fixed point form of sufficient precision.
fn main(X: [[Field; NUM_FEATURES]; EVAL_SET_SIZE], y: pub [Field; EVAL_SET_SIZE], beta: pub [Field; NUM_COEFFS], regularization_constraint: pub Field) -> pub (Field, Field) {    
    let mut predictions = [0; EVAL_SET_SIZE];
    // Populate predictions
    for i in 0..EVAL_SET_SIZE {
        let mut total = FIXED_POINT_ZERO;
        for j in 0..NUM_FEATURES {
            let product = fixed_point_multiply(X[i][j], beta[j]);
            total = fixed_point_add(total, product);
        }
        total = fixed_point_add(total, beta[NUM_FEATURES]); // Add in bias term.

        predictions[i] = total;
    }

    let mut l2_loss = FIXED_POINT_ZERO;
    // Compute the loss. Do need to be careful about fixed point here.
    for i in 0..EVAL_SET_SIZE {
        let diff = fixed_point_subtract(predictions[i], y[i]);
        let squared_error = fixed_point_multiply(diff, diff);
        l2_loss = fixed_point_add(l2_loss, squared_error);
    }
    
    // Enforce the L1 regularization constraint.
    // Need to build a fixed point zero here.
    let mut l1_norm = FIXED_POINT_ZERO;
    for i in 0..NUM_COEFFS {
        let (coeff, _) = fixed_point_abs(beta[i]);
        l1_norm = fixed_point_add(l1_norm, coeff);
    }
    assert(fixed_point_lte(l1_norm, regularization_constraint));

    // Compute the average of predictions.
    let mut prediction_sum: Field = FIXED_POINT_ZERO;
    for i in 0..EVAL_SET_SIZE {
        prediction_sum = fixed_point_add(prediction_sum, predictions[i]);
    }
    let inverse_eval_set_size = (RIGHT_SHIFT_FACTOR) as u128;
    let inverse_eval_set_size_u128 = inverse_eval_set_size / (EVAL_SET_SIZE as u128); // Integer division.
    let inverse_eval_set_size = (inverse_eval_set_size_u128 as Field) + FIXED_POINT_ZERO;
    let average_prediction = fixed_point_multiply(prediction_sum, inverse_eval_set_size);

    let mut prediction_avg_sum_of_square_differences: Field = FIXED_POINT_ZERO;
    for i in 0..EVAL_SET_SIZE {
        let diff = fixed_point_subtract(predictions[i], average_prediction);
        let squared_diff = fixed_point_multiply(diff, diff);
        prediction_avg_sum_of_square_differences = fixed_point_add(prediction_avg_sum_of_square_differences, squared_diff);
    }

    // Pulling a prio here, R^2 needs to be computed from these.
    (l2_loss, prediction_avg_sum_of_square_differences)
}

// Returns quotient and remainder of right shifting val by some amount.
// Shift amount is in bytes since this depends on that.
unconstrained fn right_shift(val: Field, shift_amount: u32) -> (Field, Field) {
    let bytes = val.to_le_bytes::<32>();
    let mut shifted_bytes = [0; 32];
    let mut remainder_bytes = [0; 32];

    for i in 0..(32 - shift_amount) {
        shifted_bytes[i] = bytes[i + shift_amount];
    }

    for i in 0..shift_amount {
        remainder_bytes[i] = bytes[i];   
    }

    let shifted = Field::from_le_bytes::<32>(shifted_bytes);
    let remainder = Field::from_le_bytes::<32>(remainder_bytes);

    (shifted, remainder)
}

// Multiply 2 values in fixed point representation, with FIXED_POINT_PRECISION_BYTES of precision,
// and ZERO biased to FIXED_POINT_ZERO.
fn fixed_point_multiply(x: Field, y: Field) -> Field {
    let (x_pos, x_is_neg) = fixed_point_abs(x);
    let (y_pos, y_is_neg) = fixed_point_abs(y);

    let x_unbiased = x_pos - FIXED_POINT_ZERO;
    let y_unbiased = y_pos - FIXED_POINT_ZERO;

    let prod = x_unbiased * y_unbiased;

    // Safety: we do range checks after the shift to ensure correctness.
    let (shifted, remainder) = unsafe { right_shift(prod, FIXED_POINT_PRECISION_BYTES) };

    assert(shifted * RIGHT_SHIFT_FACTOR + remainder == prod); // range check
    remainder.assert_max_bit_size::<FIXED_POINT_PRECISION_BYTES * 8>();
    
    let result_is_neg = x_is_neg != y_is_neg;
    if result_is_neg {
        FIXED_POINT_ZERO - shifted
    } else {
        FIXED_POINT_ZERO + shifted
    }
}

fn fixed_point_add(x: Field, y: Field) -> Field {
    x + y - FIXED_POINT_ZERO
}

fn fixed_point_subtract(x: Field, y: Field) -> Field {
    x - y + FIXED_POINT_ZERO
}

unconstrained fn is_negative_hint(x: Field) -> bool {
    let x_bytes = x.to_le_bytes::<32>();
    let z_bytes = FIXED_POINT_ZERO.to_le_bytes::<32>();
    
    // Implement Field comparison on bytes, which we do have access to.
    let mut result = false;
    for i in 0..32 {
        let idx = 31 - i;
        if x_bytes[idx] != z_bytes[idx] {
            result = x_bytes[idx] < z_bytes[idx];
            break;
        }
    }
    result
}

fn fixed_point_abs(x: Field) -> (Field, bool) {
    // Safety: we do range checks to verify this is correct.
    let is_negative: bool = unsafe { is_negative_hint(x) };
    
    let abs_value = if is_negative {
        fixed_point_subtract(FIXED_POINT_ZERO, x)
    } else {
        x
    };
    
    // Check bitlength of absolute value is correct.
    let abs_unbiased = abs_value - FIXED_POINT_ZERO;
    abs_unbiased.assert_max_bit_size::<(FIXED_POINT_PRECISION_BYTES + FIXED_POINT_MAX_MAGNITUDE_BYTES) * 8>();
    
    (abs_value, is_negative)
}

// Returns true if a <= b, comparing field elements as integers via bytes.
unconstrained fn field_lte_hint(a: Field, b: Field) -> bool {
    let a_bytes = a.to_le_bytes::<32>();
    let b_bytes = b.to_le_bytes::<32>();

    let mut result = true; // Equal case: a <= b
    for i in 0..32 {
        let idx = 31 - i;
        if a_bytes[idx] != b_bytes[idx] {
            result = a_bytes[idx] < b_bytes[idx];
            break;
        }
    }
    result
}

// Returns true if a <= b for fixed-point values.
fn fixed_point_lte(a: Field, b: Field) -> bool {
    // Safety: we verify with range checks
    let a_lte_b: bool = unsafe { field_lte_hint(a, b) };

    // Compute the difference in the direction indicated by the hint
    let diff = if a_lte_b {
        b - a  // If a <= b, then b - a >= 0
    } else {
        a - b  // If a > b, then a - b > 0
    };

    // The difference must fit in our fixed-point range (be a small non-negative value)
    diff.assert_max_bit_size::<(FIXED_POINT_PRECISION_BYTES + FIXED_POINT_MAX_MAGNITUDE_BYTES) * 8>();

    a_lte_b
}