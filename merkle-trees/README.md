# Merkle Trees
This repository contains our implementations of modified Merkle Trees, which are part of our approach for verifying alignment in-circuit.

src/bin/long_leaf_benchmark.rs and src/bin/split_tree_benchmark.rs contain benchmarks for building a Merkle Tree over a full genome in plain computation, and the corresponding data structures are implemented in /src/. We also implement circuits for verifying membership in these merkle trees in files named `circuit.rs`.

We build upon Varun Thakore's implementation of Merkle Trees [here](https://github.com/varunthakore/merkle-trees/tree/master/src). All the trees use Poseidon hash function implemented by [Neptune](https://github.com/lurk-lab/neptune) and the `bellpepper` constraint library.
