# Separately test the runtime of the PCS bit. Should be run in the lasso_regression directory.
nargo check --overwrite

python3 ./scripts/generate_inputs.py

cargo run --release --manifest-path ../pcs_authentication/Cargo.toml -- Prover.toml
