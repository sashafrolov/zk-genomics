# Zero-Knowledge proofs for genomics computations.
This repository contains the code for the experiments of our paper "Icefish: Practical zk-SNARKs for Verifiable Genomics".
The subdirectories contain the code for different experiments run in the paper, as well as instructions for running it.
- `alignment-circuits` contains our demonstration code for implementing different types of alignment computations from Section 4 of the paper, as well as the combined end-to-end demo.
- `gwas-experiments` contains our demonstration code for implementing regularized linear regression from Section 6 of the paper.
- `merkle-trees` contains an early version of our code for implementing succinct data structures for Merkle Trees from Section 5 of the paper.
- `Plonky3` is a forked version of Plonky3 containing our final implementation of succinct data structures for Merkle Trees from Section 5. You can find the benchmarks and implementations of these at `Plonky3/src/bin/`.
- `zk_crispr` contains our code for implementing models related to CRISPR from Section 7 of the paper.

# Acknowledgements
- `Spartan2` is a slightly modified version of Microsoft's [Spartan2](https://github.com/microsoft/Spartan2) repository.
- We used Varun Thakore's merkle tree implementation as a basis for `merkle-trees`.
- We used [Plonky3](https://github.com/Plonky3/Plonky3) as the base for our final implementation of Merkle tree related experiments.
- We used some of the example circuits in `Spartan2` as the basis for our alignment circuits.