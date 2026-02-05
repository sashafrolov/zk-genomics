#!/bin/bash

# nargo check --overwrite
/usr/bin/time -v nargo execute my_witness &> witness_out.txt
bb write_vk -b ./target/merkle_tree_gen.json -o ./target
# /usr/bin/time -v bb prove -vb target/merkle_tree_gen.json -w target/my_witness.gz -o proof
/usr/bin/time -v bb prove -vb target/merkle_tree_gen.json -w target/my_witness.gz -o target &> prove_out.txt
bb gates -b ./target/merkle_tree_gen.json &> gates.txt

time bb verify -k target/vk -p target/proof
#!/bin/bash


# Set your variable
total_runs=80

# 1. Capture start time in seconds.nanoseconds
start_time=$(date +%s.%N)

# --- Your Command Here ---
# Example: sleep for 1.23 seconds to test
for (( i=1; i<=total_runs; i++ ))
do
    bb prove -vb target/merkle_tree_gen.json -w target/my_witness.gz -o target
done
# -------------------------

# 2. Capture end time
end_time=$(date +%s.%N)

# 3. Calculate duration using bc (arbitrary precision calculator)
# We calculate the difference and use printf to ensure exactly 10 decimal places
duration=$(echo "$end_time - $start_time" | bc -l)

# 4. Write to file with 10 decimal precision
LC_NUMERIC=C printf "%.10f %d\n" "$duration" "$total_runs" >> prove_runtime.txt


# Optional: Print to console to verify
echo "Witness Runtime saved: $(cat prove_runtime.txt) seconds"