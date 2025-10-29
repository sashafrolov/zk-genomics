use crate::{Base, CigarChar};

/// Computes an optimal global pairwise alignment between two DNA sequences using the
/// Needleman-Wunsch algorithm and returns a CIGAR string representation of the alignment
/// along with the alignment score.
///
/// The CIGAR operations are relative to the reference sequence (first input):
/// - Match: bases align (match or mismatch in the sequences)
/// - Insert: insertion relative to reference (gap in reference)
/// - Delete: deletion relative to reference (gap in target)
///
/// Credit to this github repo: https://github.com/kensho-technologies/sequence_align/tree/main
/// for the original source this is adapted from.
/// TODO: Unify the gap_score argument with match/mismatch score.
pub fn basic_alignment(
    reference_sequence: Vec<Base>,
    target_sequence: Vec<Base>,
    match_score: f64,
    mismatch_score: f64,
    gap_score: f64,
) -> (Vec<CigarChar>, usize) {
    let ref_len = reference_sequence.len();
    let target_len = target_sequence.len();

    // Handle empty sequences
    if ref_len == 0 && target_len == 0 {
        return (Vec::new(), 0);
    }
    if ref_len == 0 {
        return (vec![CigarChar::Insert; target_len], 0);
    }
    if target_len == 0 {
        return (vec![CigarChar::Delete; ref_len], 0);
    }

    let num_rows = ref_len + 1;
    let num_cols = target_len + 1;

    // Initialize score matrix
    let mut scores: Vec<f64> = (0..num_rows)
        .flat_map(|row_idx| {
            (0..num_cols)
                .map(|col_idx| {
                    if row_idx == 0 {
                        (col_idx as f64) * gap_score
                    } else if col_idx == 0 {
                        (row_idx as f64) * gap_score
                    } else {
                        0.0
                    }
                })
                .collect::<Vec<f64>>()
        })
        .collect();

    // Initialize backpointers matrix
    // Backpointers encode the direction: 0 = diagonal, 1 = up (delete), 2 = left (insert)
    let mut backpointers: Vec<u8> = (0..num_rows)
        .flat_map(|row_idx| {
            (0..num_cols)
                .map(|col_idx| {
                    if row_idx == 0 && col_idx > 0 {
                        2 // left (insert)
                    } else if col_idx == 0 && row_idx > 0 {
                        1 // up (delete)
                    } else {
                        0 // diagonal
                    }
                })
                .collect::<Vec<u8>>()
        })
        .collect();

    // Fill the score and backpointer matrices
    for row_idx in 1..num_rows {
        let ref_idx = row_idx - 1;
        for col_idx in 1..num_cols {
            let cell_idx = (row_idx * num_cols) + col_idx;
            let target_idx = col_idx - 1;

            // Check if match or mismatch
            let compare_score = if reference_sequence[ref_idx] == target_sequence[target_idx] {
                match_score
            } else {
                mismatch_score
            };

            // Score transitions from diagonal, up, and left
            let diagonal_idx = cell_idx - num_cols - 1;
            let diagonal_score = scores[diagonal_idx] + compare_score;

            let up_idx = cell_idx - num_cols;
            let up_score = scores[up_idx] + gap_score;

            let left_idx = cell_idx - 1;
            let left_score = scores[left_idx] + gap_score;

            // Pick the best transition (prioritize diagonal, then left, then up for ties)
            let (transition_score, transition_direction) =
                if diagonal_score >= up_score && diagonal_score >= left_score {
                    (diagonal_score, 0) // diagonal
                } else if left_score >= up_score {
                    (left_score, 2) // left (insert)
                } else {
                    (up_score, 1) // up (delete)
                };

            scores[cell_idx] = transition_score;
            backpointers[cell_idx] = transition_direction;
        }
    }

    // Traceback to build CIGAR string
    let mut cigar = Vec::new();
    let mut row_idx = ref_len;
    let mut col_idx = target_len;

    while row_idx > 0 || col_idx > 0 {
        let cell_idx = (row_idx * num_cols) + col_idx;
        let direction = backpointers[cell_idx];

        match direction {
            0 => {
                // Diagonal: Match (covers both actual matches and mismatches)
                cigar.push(CigarChar::Match);
                row_idx -= 1;
                col_idx -= 1;
            }
            1 => {
                // Up: Delete (gap in target, base consumed from reference)
                cigar.push(CigarChar::Delete);
                row_idx -= 1;
            }
            2 => {
                // Left: Insert (gap in reference, base consumed from target)
                cigar.push(CigarChar::Insert);
                col_idx -= 1;
            }
            _ => unreachable!(),
        }
    }

    // Reverse CIGAR string (we built it backwards)
    cigar.reverse();

    // Get final alignment score
    let final_score = scores[(num_rows * num_cols) - 1];
    let final_score_usize = final_score.round() as usize;

    (cigar, final_score_usize)
}

pub fn affine_gap_alignment(
    reference_sequence: Vec<Base>,
    target_sequence: Vec<Base>,
    gap_start_score: f64,
    match_score: f64,
    mismatch_score: f64,
) -> (Vec<CigarChar>, u32) {
    todo!("Not yet implemented");
}

// Variants and how to deal with them:
// Semiglobal/global: do the main body of the clipping outside of our alignment code.
// Affine: do here
// Multiple sequence alignment: not yet sure.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_alignment_simple() {
        let reference = vec![Base::A, Base::C, Base::G, Base::T];
        let target = vec![Base::A, Base::G, Base::T];

        let (cigar, score) = basic_alignment(reference, target, 1.0, -1.0, -1.0);

        println!("CIGAR: {:?}", cigar);
        println!("Score: {}", score);

        assert_eq!(cigar.len(), 4);
        assert_eq!(cigar[0], CigarChar::Match);
        assert_eq!(cigar[1], CigarChar::Delete);
        assert_eq!(cigar[2], CigarChar::Match);
        assert_eq!(cigar[3], CigarChar::Match);
    }

    #[test]
    fn test_basic_alignment_with_insertion() {
        let reference = vec![Base::A, Base::G, Base::T];
        let target = vec![Base::A, Base::C, Base::G, Base::T];

        let (cigar, score) = basic_alignment(reference, target, 1.0, -1.0, -1.0);

        println!("CIGAR: {:?}", cigar);
        println!("Score: {}", score);

        assert_eq!(cigar.len(), 4);
        assert_eq!(cigar[0], CigarChar::Match);
        assert_eq!(cigar[1], CigarChar::Insert);
        assert_eq!(cigar[2], CigarChar::Match);
        assert_eq!(cigar[3], CigarChar::Match);
    }

    // fn test_basic_alignment_with_gap() {
    //     let reference = vec![Base::T, Base::C, Base::G, Base::T];
    //     let target = vec![Base::A, Base::C, Base::G, Base::T];

    //     let (cigar, score) = basic_alignment(
    //         reference,
    //         target,
    //         1.0,
    //         -1.0,
    //         -1.0,
    //     );

    //     println!("CIGAR: {:?}", cigar);
    //     println!("Score: {}", score);

    //     assert_eq!(cigar.len(), 4);
    //     assert_eq!(cigar[0], CigarChar::Match);
    //     assert_eq!(cigar[1], CigarChar::Insert);
    //     assert_eq!(cigar[2], CigarChar::Match);
    //     assert_eq!(cigar[3], CigarChar::Match);
    // }

    #[test]
    fn test_basic_alignment_perfect_match() {
        // Test case: perfect match
        let sequence = vec![Base::A, Base::C, Base::G, Base::T];

        let (cigar, score) = basic_alignment(sequence.clone(), sequence.clone(), 1.0, -1.0, -1.0);

        println!("CIGAR: {:?}", cigar);
        println!("Score: {}", score);

        assert_eq!(cigar.len(), 4);
        assert!(cigar.iter().all(|&c| c == CigarChar::Match));
        assert_eq!(score, 4);
    }

    #[test]
    fn test_basic_alignment_empty_sequences() {
        let (cigar, score) = basic_alignment(vec![], vec![], 1.0, -1.0, -1.0);

        assert_eq!(cigar.len(), 0);
        assert_eq!(score, 0);
    }

    #[test]
    fn test_basic_alignment_one_empty() {
        let reference = vec![Base::A, Base::C, Base::G];

        let (cigar, score) = basic_alignment(reference.clone(), vec![], 1.0, -1.0, -1.0);

        // All deletes
        assert_eq!(cigar.len(), 3);
        assert!(cigar.iter().all(|&c| c == CigarChar::Delete));
    }
}
