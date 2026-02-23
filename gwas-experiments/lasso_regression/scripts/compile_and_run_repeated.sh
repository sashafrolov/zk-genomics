#!/bin/bash

# This runs all the different commands to compile, generate inputs and run
# a Noir script. This assumes that you are in the lasso_regression directory
# and should be run as `./scripts/compile_and_run.sh`.

for i in {1..1000}; do
    echo -e "\033[0;36m========================================\033[0m"
    echo -e "\033[0;36m===== Iteration $i of 100 =====\033[0m"
    echo -e "\033[0;36m========================================\033[0m"

    echo -e "\033[0;32m===== Setting Up Proofs =====\033[0m"
    # Produce the empty Prover.toml file
    nargo check --overwrite

    # Populate the Prover.toml file with inputs
    python3 ./scripts/generate_inputs.py

    # Generate a witness
    nargo execute

    # Generate a VK (need to do this separately for accurate performance numbers)
    bb write_vk -b ./target/lasso_regression.json -o ./target

    echo -e "\033[0;32m===== Generating Gate Counts =====\033[0m"
    # Generate gate count
    bb gates -b ./target/lasso_regression.json

    echo -e "\033[0;32m===== Timing Proof Generation =====\033[0m"
    # Actually compute the proof
    time bb prove -b ./target/lasso_regression.json -w ./target/lasso_regression.gz -o ./target --vk_path ./target/vk

    echo -e "\033[0;32m===== Timing verification =====\033[0m"
    # Verify the proof
    time bb verify -p ./target/proof -k ./target/vk
done
