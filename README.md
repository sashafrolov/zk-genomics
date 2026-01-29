# Zero-Knowledge proofs for genomics computations.
This repository contains the code for the experiments of our paper "Icefish: Practical zk-SNARKs for Genomic Computations".
The subdirectories contain the code for different experiments run in the paper, as well as instructions for running it.
- `alignment-circuits` contains our demonstration code for implementing different types of alignment computations from Section N in the paper, as well as the combined end-to-end demo.
- `gwas-experiments` contains our demonstration code for implementing regularized linear regression from Section N in the paper.
- `merkle-trees` contains our code for implementing succinct data structures

# Acknowledgements
- `Spartan2` is a slightly modified version of Microsoft's [Spartan2](https://github.com/microsoft/Spartan2) repository.
- We used Varun Thakore's merkle tree implementation as a basis for `merkle-trees`.
- We used some of the example circuits in `Spartan2` as the basis for our circuits.