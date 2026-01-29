pub mod alignment_plain_computation;

// use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ff::{PrimeField, PrimeFieldBits};
use rand::RngCore;

use bellpepper::gadgets::multipack::compute_multipacking;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Base {
    A,
    C,
    G,
    T,
}

impl Base {
    pub fn to_field<F: PrimeField + PrimeFieldBits>(&self) -> F {
        match self {
            Base::A => F::from(0u64),
            Base::C => F::from(1u64),
            Base::G => F::from(2u64),
            Base::T => F::from(3u64),
        }
    }

    pub fn to_bool_pair(&self) -> (bool, bool) {
        match self {
            Base::A => (false, false),
            Base::C => (true, false),
            Base::G => (false, true),
            Base::T => (true, true),
        }
    }

    pub fn from_field<F: PrimeField + PrimeFieldBits>(x: F) -> Option<Self> {
        // Convert to a u64, assuming the value fits in 0..3
        let (b1, b2) = (x.to_le_bits()[1], x.to_le_bits()[0]);
        match (b1, b2) {
            (false, false) => Some(Base::A),
            (false, true) => Some(Base::C),
            (true, false) => Some(Base::G),
            (true, true) => Some(Base::T),
        }
    }

    pub fn random_sequence(n: usize) -> Vec<Base> {
        let mut rng = rand::thread_rng();
        (0..n)
            .map(|_| match rng.next_u32() % 4 {
                0 => Base::A,
                1 => Base::C,
                2 => Base::G,
                3 => Base::T,
                _ => panic!("What the heck?"),
            })
            .collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CigarChar {
    Match,
    Insert,
    Delete,
    Clip, // Especially the Clip character is based on a very loose interpretation of the CIGAR standard.
}

impl CigarChar {
    pub fn to_field<F: PrimeField>(&self) -> F {
        match self {
            CigarChar::Match => F::from(0u64),
            CigarChar::Insert => F::from(1u64),
            CigarChar::Delete => F::from(2u64),
            CigarChar::Clip => F::from(3u64),
        }
    }

    pub fn from_field<F: PrimeField + PrimeFieldBits>(x: F) -> Option<Self> {
        let (b1, b2) = (x.to_le_bits()[1], x.to_le_bits()[0]);
        match (b1, b2) {
            (false, false) => Some(CigarChar::Match),
            (false, true) => Some(CigarChar::Insert),
            (true, false) => Some(CigarChar::Delete),
            (true, true) => Some(CigarChar::Clip),
        }
    }

    pub fn to_bool_pair(&self) -> (bool, bool) {
        match self {
            CigarChar::Match => (false, false),
            CigarChar::Insert => (true, false),
            CigarChar::Delete => (false, true),
            CigarChar::Clip => (true, true),
        }
    }
}

pub trait ToFeltBlocks {
    fn to_felt_blocks<F: PrimeField + PrimeFieldBits>(&self, bases_per_block: usize) -> Vec<F>;
}

impl ToFeltBlocks for Vec<Base> {
    fn to_felt_blocks<F: PrimeField + PrimeFieldBits>(&self, bases_per_block: usize) -> Vec<F> {
        let mut base_chunks = Vec::new();
        for chunk in self.chunks(bases_per_block) {
            let chunk_as_bools = chunk
                .into_iter()
                .map(|base| vec![base.to_bool_pair().0, base.to_bool_pair().1])
                .flatten()
                .collect::<Vec<_>>();

            let chunk_felt = compute_multipacking(&chunk_as_bools);
            base_chunks.push(chunk_felt[0]);
        }
        base_chunks
    }
}

impl ToFeltBlocks for Vec<CigarChar> {
    fn to_felt_blocks<F: PrimeField + PrimeFieldBits>(&self, chars_per_block: usize) -> Vec<F> {
        let mut base_chunks = Vec::new();
        for chunk in self.chunks(chars_per_block) {
            let chunk_as_bools = chunk
                .into_iter()
                .map(|base| vec![base.to_bool_pair().0, base.to_bool_pair().1])
                .flatten()
                .collect::<Vec<_>>();

            let chunk_felt = compute_multipacking(&chunk_as_bools);
            base_chunks.push(chunk_felt[0]);
        }
        base_chunks
    }
}

// Analogue of a CIGAR character for multiple sequence alignment. Not quite the same thing, wanted to distinguish.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MSACigarChar {
    Match,
    Gap,
}

impl MSACigarChar {
    pub fn to_field<F: PrimeField>(&self) -> F {
        match self {
            MSACigarChar::Match => F::from(0u64),
            MSACigarChar::Gap => F::from(1u64),
        }
    }

    pub fn from_field<F: PrimeField + PrimeFieldBits>(x: F) -> Option<Self> {
        let b = x.to_le_bits()[0];
        match b {
            false => Some(MSACigarChar::Match),
            true => Some(MSACigarChar::Gap),
        }
    }

    pub fn to_bool(&self) -> bool {
        match self {
            MSACigarChar::Match => false,
            MSACigarChar::Gap => true,
        }
    }
}

impl ToFeltBlocks for Vec<MSACigarChar> {
    fn to_felt_blocks<F: PrimeField + PrimeFieldBits>(&self, chars_per_block: usize) -> Vec<F> {
        let mut base_chunks = Vec::new();
        for chunk in self.chunks(chars_per_block) {
            let chunk_as_bools = chunk
                .into_iter()
                .map(|msa_char| msa_char.to_bool())
                .collect::<Vec<_>>();

            let chunk_felt = compute_multipacking(&chunk_as_bools);
            base_chunks.push(chunk_felt[0]);
        }
        base_chunks
    }
}
