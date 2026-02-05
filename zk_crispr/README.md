# zk_crispr

The main_<INFO> are the main files for different algorithms.

* main_off.nr - For off-target (MIT Score)
* main_on.nr - For on-target Rule Set One
* main_comb.nr - For evaluating a sequence where it is publicly known which are for on-target and which is off target.
  Those indices are hard-coded into the circuit.
* main_comb_hidden.nr - For evaluating a sequence where it is privately known which are for on-target and which is off
  target.

Within the "src/membership.nr" file where "INPUT_LEN" and "MAX_DEPTH" (ceiling(long2(INPUT_LEN))) are specified.

To run benchmarks, move the targetted main file to "src/main.rs" and change "src/membership.rs" as needed.
To run just on or off target scoring or combined scoring with public indices, run "./prep.sh" and then "
./prove_bench.sh". In prove_bench.sh has the "total_runs" variable.

To run the combined scoring with public indices, run "./prep_comb_hideen.sh" (where private inputs for the indices are
defined in update_prover_hidden.py) and then "
./prove_bench.sh". In prove_bench.sh has the "total_runs" variable.
