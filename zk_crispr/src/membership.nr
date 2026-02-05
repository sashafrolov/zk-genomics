//use dep::std;
use poseidon::poseidon2::Poseidon2;

// Adjust DEPTH based on your tree size (log2 of number of leaves)
pub global INPUT_LEN: u32 = 100;
global MAX_DEPTH: u32 = 7; // log2(5) rounded up

// Sponge construction parameters
global STATE_SIZE: u32 = 5;
global RATE: u32 = 4;        // Number of elements to absorb per permutation
global CAPACITY: u32 = 1;    // Security parameter (128-bit security)
// Sponge-like construction parameters
global CHUNK_SIZE: u32 = 4;  // Process 4 elements at a time


/// Hash two field elements using Poseidon2
pub fn hash_pair(left: Field, right: Field) -> Field {
    Poseidon2::hash([left, right], 2)
}

/// Compute Merkle root iteratively to avoid recursion issues
pub fn compute_merkle_root<let N: u32>(leaves: [Field; N]) -> Field {
    let mut current_layer: [Field; N] = leaves;
    let mut current_len = N;

    // Iteratively build layers until we reach the root
    for _depth in 0..MAX_DEPTH {
        let next_len = (current_len + 1) / 2;
        let mut next_layer = [0; N];

        for i in 0..N {
            if i < next_len {
                let left_idx = i * 2;
                let right_idx = i * 2 + 1;

                let left = current_layer[left_idx];
                let right = if right_idx < current_len {
                    current_layer[right_idx]
                } else {
                    0
                };

                next_layer[i] = hash_pair(left, right);
            }
        }

        current_layer = next_layer;
        current_len = next_len;
    }

    current_layer[0]
}

/// Efficient commitment using chunked hashing
/// Process multiple elements before hashing, reducing total hash operations
pub fn commit_to_list<let N: u32>(elements: [Field; N]) -> Field {
    let mut state = 0;
    let mut chunk = [0; CHUNK_SIZE];
    let mut chunk_pos = 0;

    for i in 0..N {
        chunk[chunk_pos] = elements[i];
        chunk_pos = chunk_pos + 1;

        // Hash the chunk when full or at the end
        let should_hash = (chunk_pos == CHUNK_SIZE) | (i == N - 1);

        if should_hash {
            // Hash the state with all accumulated chunk elements
            if chunk_pos == 1 {
                state = Poseidon2::hash([state, chunk[0]], 2);
            } else if chunk_pos == 2 {
                state = Poseidon2::hash([state, chunk[0], chunk[1]], 3);
            } else if chunk_pos == 3 {
                state = Poseidon2::hash([state, chunk[0], chunk[1], chunk[2]], 4);
            } else {
                state = Poseidon2::hash([state, chunk[0], chunk[1], chunk[2], chunk[3]], 5);
            }

            // Reset chunk
            chunk = [0; CHUNK_SIZE];
            chunk_pos = 0;
        }
    }

    state
}

/// Alternative: Sequential hashing (simpler but less efficient)
/// This performs one hash per element: ~100,000 hashes
pub fn commit_to_list_sequential<let N: u32>(elements: [Field; N]) -> Field {
    let mut accumulator = 0;

    for i in 0..N {
        accumulator = hash_pair(accumulator, elements[i]);
    }

    accumulator
}


pub fn memb_main(leaves: [Field; INPUT_LEN]) -> Field {
    //compute_merkle_root(leaves)
    //commit_to_list_sequential(leaves)
    commit_to_list(leaves)
}