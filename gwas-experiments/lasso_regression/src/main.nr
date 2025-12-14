global EVAL_SET_SIZE: u32 = 100;
global NUM_FEATURES: u32 = 999; // This is not sparse, may change later.
global NUM_COEFFS: u32 = NUM_FEATURES + 1; // There is an additional bias term.

// X is the set of data points in the evaluation set.
// y is the set of expected outputs for the evaluation set.
// beta is the set of claimed coefficients, which is public.
// target_loss is the value that loss must be less than.
// All of these values must be in fixed point form of sufficient precision.
fn main(X: [[Field; NUM_FEATURES]; EVAL_SET_SIZE], y: pub [Field; EVAL_SET_SIZE], beta: pub [Field; NUM_COEFFS], target_loss: pub Field) {
    let mut predictions = [0; EVAL_SET_SIZE];
    // Populate predictions
    for i in 0..EVAL_SET_SIZE {
        let mut total = 0;
        for j in 0..NUM_FEATURES {
            total += X[i][j] * beta[j];
        }
        total += beta[NUM_FEATURES];
        predictions[i] = total;
    }

    let mut l2_loss = 0;
    // Compute the loss. Do need to be careful about fixed point here.
    for i in 0..EVAL_SET_SIZE {
        let diff = predictions[i] - y[i];
        let squared_error = diff * diff;
        l2_loss += squared_error;
    }
    assert(l2_loss == target_loss);
}

