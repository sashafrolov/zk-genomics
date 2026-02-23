#!/usr/bin/env python3
import pathlib
import random
import sys
import numpy as np
import tomllib
import tomli_w
from sklearn.linear_model import LassoCV
from sklearn.datasets import make_regression

# Recording relevant magnitudes of values in QTL-MAS dataset.
# Phenotypes range from 0-100, 2 digits decimal precision, binary explanation variables.
# Pedigree: Integer 0-5000, binary sex.
# Marker info goes up to 100 million, not sure what it means.
# Marker alleles are like 0/1/2, but very many.

# Fixed-point constants matching main.nr
FIXED_POINT_PRECISION_BYTES = 4
FIXED_POINT_MAX_MAGNITUDE_BYTES = 4
FIXED_POINT_SCALE = 2 ** (FIXED_POINT_PRECISION_BYTES * 8)  # 2^32
FIXED_POINT_ZERO = 2 ** ((FIXED_POINT_PRECISION_BYTES + FIXED_POINT_MAX_MAGNITUDE_BYTES) * 8)  # 2^64


def to_fixed_point(value: float) -> int:
    """
    Convert a float to fixed-point representation matching Noir's format.
    Values are scaled by 2^32 and biased by 2^64 (so zero maps to 2^64).
    """
    scaled = int(value * FIXED_POINT_SCALE)
    return scaled + FIXED_POINT_ZERO

def generate_synthetic_data(eval_set_size: int, num_features: int, n_informative: int = 10, noise: float = 1.0, random_state: int = 42):
    """
    Generate synthetic regression data suitable for Lasso.
    """
    X, y = make_regression(
        n_samples=eval_set_size,
        n_features=num_features,
        n_informative=n_informative,
        noise=noise,
        random_state=random_state
    )
    # TODO: Experiment with scaling feature matrix to see how this impacts performance.
    return X, y


def fit_lasso(X: np.ndarray, y: np.ndarray, cv: int = 5):
    """
    Fit a Lasso regression model with cross-validation.
    Returns model and beta (coefficients with bias term last).
    """
    model = LassoCV(cv=cv)
    model.fit(X, y)

    # Combine coefficients and intercept (bias term last, matching Noir convention)
    beta = np.append(model.coef_, model.intercept_)

    return model, beta


def main():
    # Path to Prover.toml
    config_path = pathlib.Path("Prover.toml")

    if not config_path.exists():
        sys.stderr.write(f"Error: {config_path} does not exist.\n")
        sys.exit(1)

    # Open TOML file
    with config_path.open("rb") as f:
        prover_inputs = tomllib.load(f)

    eval_set_size = len(prover_inputs['y'])
    num_coeffs = len(prover_inputs['beta'])
    num_features = len(prover_inputs['X'][0])

    # Generate synthetic data
    X, y = generate_synthetic_data(eval_set_size, num_features)

    # Fit Lasso regression
    model, beta = fit_lasso(X, y)

    # Report results
    r2_score = model.score(X, y)
    l2_loss = np.sum((y - model.predict(X)) ** 2)
    l1_norm = np.sum(np.abs(beta))
    n_nonzero = np.sum(model.coef_ != 0)

    print(f"Dataset: {eval_set_size} samples, {num_features} features")
    print(f"Best alpha (regularization): {model.alpha_:.6f}")
    print(f"R Squared score: {r2_score:.6f}")
    print(f"L2 loss (SSE): {l2_loss:.6f}")
    print(f"L1 norm of coefficients: {l1_norm:.6f}")
    print(f"Non-zero coefficients: {n_nonzero} / {num_features}")

    # Convert to fixed-point representation for Noir
    X_fixed = [[str(to_fixed_point(val)) for val in row] for row in X]
    y_fixed = [str(to_fixed_point(val)) for val in y]
    beta_fixed = [str(to_fixed_point(val)) for val in beta]
    # Max representable fixed-point value: FIXED_POINT_ZERO + (2^64 - 1) = 2^65 - 1
    max_unbiased = 2 ** ((FIXED_POINT_PRECISION_BYTES + FIXED_POINT_MAX_MAGNITUDE_BYTES) * 8) - 1
    regularization_constraint = str(FIXED_POINT_ZERO + max_unbiased)

    prover_inputs['X'] = X_fixed
    prover_inputs['y'] = y_fixed
    prover_inputs['beta'] = beta_fixed
    prover_inputs['regularization_constraint'] = regularization_constraint
    prover_inputs['challenge'] = str(random.randint(0, 2**250 - 1))

    with config_path.open("wb") as f:
        f.write(tomli_w.dumps(prover_inputs).encode("utf-8"))

if __name__ == "__main__":
    main()