#!/usr/bin/env python3
import pathlib
import random
import sys
import numpy as np
import tomllib
import tomli_w

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

    X = [[0 for _ in range(num_features)] for _ in range(eval_set_size)]
    y = [0 for _ in range(eval_set_size)]
    beta = [0 for _ in range(num_coeffs)]
    target_loss = 0

    prover_inputs['X'] = X
    prover_inputs['y'] = y
    prover_inputs['beta'] = beta
    prover_inputs['target_loss'] = target_loss

    with config_path.open("wb") as f:
        f.write(tomli_w.dumps(prover_inputs).encode("utf-8"))

if __name__ == "__main__":
    main()