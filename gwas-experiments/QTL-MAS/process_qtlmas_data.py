#!/usr/bin/env python3
import pathlib
import random
import sys
import numpy as np
import tomli_w
from sklearn.linear_model import LassoCV
from sklearn.linear_model import Lasso

# Fixed-point constants matching main.nr (Updated to 64-bit / 8 bytes)
FIXED_POINT_PRECISION_BYTES = 8
FIXED_POINT_MAX_MAGNITUDE_BYTES = 8
FIXED_POINT_SCALE = 2 ** (FIXED_POINT_PRECISION_BYTES * 8)  # 2^64
FIXED_POINT_ZERO = 2 ** ((FIXED_POINT_PRECISION_BYTES + FIXED_POINT_MAX_MAGNITUDE_BYTES) * 8)  # 2^128

def to_fixed_point(value: float) -> int:
    """
    Convert a float to fixed-point representation matching Noir's format.
    Values are scaled by 2^32 and biased by 2^64 (so zero maps to 2^64).
    """
    scaled = int(value * FIXED_POINT_SCALE)
    return scaled + FIXED_POINT_ZERO


def load_data(markers_path: str, phenotypes_path: str):
    print(f"Loading markers from {markers_path}...")
    X_raw = []
    with open(markers_path, 'r') as f:
        for line in f:
            line = line.strip()
            if not line: continue

            if ' ' in line or '\t' in line:
                features = [float(val) for val in line.split()]
            else:
                features = [float(val) for val in list(line)]
            X_raw.append(features)

    X_raw = np.array(X_raw)

    # X_raw shape is (3226, 20063).
    # Col 0 is ID. Cols 1 to 20062 are the 10031 allele pairs.
    print(f"Raw X shape: {X_raw.shape}. Combining allele pairs...")

    # We drop the ID column, then add allele 1 (cols 1, 3, 5...) and allele 2 (cols 2, 4, 6...)
    X_snps = X_raw[:, 1::2] + X_raw[:, 2::2]
    print(f"Processed X shape: {X_snps.shape}")
    assert X_snps.shape[1] == 10031, f"Expected 10031 features, got {X_snps.shape[1]}"

    # The total number of individuals in the markers file is 3226
    num_individuals = X_snps.shape[0]

    print(f"Loading phenotypes from {phenotypes_path}...")
    y_full = np.zeros(num_individuals)
    valid_train_indices = []

    with open(phenotypes_path, 'r') as f:
        for line in f:
            parts = line.strip().split()
            if len(parts) < 2:
                continue

            # parts[0] is the 1-based ID, so 0-based index is ID - 1
            idx = int(parts[0]) - 1
            # parts[1] is the quantitative trait
            y_full[idx] = float(parts[1])
            valid_train_indices.append(idx)

    print(f"Found {len(valid_train_indices)} labeled individuals for training and evaluation.")
    return X_snps, y_full, valid_train_indices


def fit_lasso(X: np.ndarray, y: np.ndarray, cv: int = 5):
    """
    Fit a Lasso regression model with cross-validation.
    Returns model and beta (coefficients with bias term last).
    """
    print(f"Fitting LassoCV on {X.shape[0]} samples and {X.shape[1]} features...")
    print("(This may take a moment, using all CPU cores)...")

    #model = LassoCV(
    #    cv=cv,
    #    max_iter=10000,
    #    selection='random',
    #    n_jobs=-1,
    #    random_state=42,
    #    n_alphas=20,     # <-- Search only 20 alphas instead of 100 (5x faster)
    #    tol=1e-2         # <-- Looser convergence tolerance (stops iterations much earlier)
    #)

    # max_iter increased and selection='random' to ensure fast convergence
    #model = LassoCV(cv=cv, max_iter=10000, selection='random', n_jobs=-1, random_state=42)
    # Train exactly ONE model using the alpha we found earlier
    model = Lasso(
        alpha=0.121688,
        max_iter=10000,
        selection='random',
        random_state=42,
        tol=1e-3
    )
    model.fit(X, y)

    # Combine coefficients and intercept (bias term last, matching Noir convention)
    beta = np.append(model.coef_, model.intercept_)

    return model, beta


def main():
    markers_file = "genotypes.txt"       # <-- Replace with actual file name if different
    phenotypes_file = "phenotypes.txt" # <-- Replace with actual file name if different

    if not pathlib.Path(markers_file).exists() or not pathlib.Path(phenotypes_file).exists():
        sys.stderr.write(f"Error: Could not find '{markers_file}' or '{phenotypes_file}'.\n")
        sys.exit(1)

    # 1. Load Data
    X, y_full, train_indices = load_data(markers_file, phenotypes_file)

    # 2. Extract ONLY the labeled data (2326 individuals)
    X_train = X[train_indices]
    y_train = y_full[train_indices]
    eval_set_size = X_train.shape[0]
    num_features = X_train.shape[1]

    # 3. Fit Lasso regression
    model, beta = fit_lasso(X_train, y_train)

    # 4. Report results
    r2_score = model.score(X_train, y_train)
    l2_loss = np.sum((y_train - model.predict(X_train)) ** 2)
    l1_norm = np.sum(np.abs(beta))
    n_nonzero = np.sum(model.coef_ != 0)

    print("\n===== Model Summary =====")
    print(f"Dataset: {eval_set_size} samples, {num_features} features")
    #print(f"Best alpha (regularization): {model.alpha_:.6f}")
    print(f"Best alpha (regularization): {model.alpha:.64f}")
    print(f"R Squared score: {r2_score:.64f}")
    print(f"L2 loss (SSE): {l2_loss:.64f}")
    print(f"L1 norm of coefficients: {l1_norm:.64f}")
    print(f"Non-zero coefficients: {n_nonzero} / {num_features}")

    # 5. Convert to fixed-point representation for Noir
    print("\nConverting variables to fixed-point representations...")
    # We export ONLY the labeled 2326 rows so the circuit evaluates properly
    X_fixed = [[str(to_fixed_point(val)) for val in row] for row in X_train]
    y_fixed = [str(to_fixed_point(val)) for val in y_train]
    beta_fixed = [str(to_fixed_point(val)) for val in beta]

    # Max representable fixed-point value: FIXED_POINT_ZERO + (2^64 - 1) = 2^65 - 1
    max_unbiased = 2 ** ((FIXED_POINT_PRECISION_BYTES + FIXED_POINT_MAX_MAGNITUDE_BYTES) * 8) - 1
    regularization_constraint = str(FIXED_POINT_ZERO + max_unbiased)

    prover_inputs = {
        'X': X_fixed,
        'y': y_fixed,
        'beta': beta_fixed,
        'regularization_constraint': regularization_constraint,
        'challenge': str(random.randint(0, 2**250 - 1))
    }

    # 6. Write out to Prover.toml
    config_path = pathlib.Path("Prover.toml")
    with config_path.open("wb") as f:
        f.write(tomli_w.dumps(prover_inputs).encode("utf-8"))

    print(f"Successfully wrote inputs to {config_path.absolute()}")

if __name__ == "__main__":
    main()
