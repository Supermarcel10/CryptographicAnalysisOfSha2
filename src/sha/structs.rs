use std::fmt::{Debug, Display, Formatter, LowerHex};
use crate::verification::bit_differential::BitDifferential;

// Math implemented as defined on Wikipedia https://en.wikipedia.org/wiki/SHA-2
pub trait Word: Copy + PartialEq + Default + Debug + LowerHex + BitDifferential {
	fn ch(e: Self, f: Self, g: Self) -> Self;
	fn maj(a: Self, b: Self, c: Self) -> Self;
	fn sigma0(a: Self) -> Self;
	fn sigma1(e: Self) -> Self;
	fn gamma0(x: Self) -> Self;
	fn gamma1(x: Self) -> Self;
	fn from_be_bytes(bytes: &[u8]) -> Self;
	fn wrapping_add(self, rhs: Self) -> Self;
	fn from_u64_vec(slice: Vec<u64>) -> Vec<Self>;
}

impl Word for u32 {
	fn ch(e: Self, f: Self, g: Self) -> Self {
		(e & f) ^ (!e & g)
	}

	fn maj(a: Self, b: Self, c: Self) -> Self {
		(a & b) ^ (a & c) ^ (b & c)
	}

	fn sigma0(a: Self) -> Self {
		a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22)
	}

	fn sigma1(e: Self) -> Self {
		e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25)
	}

	fn gamma0(x: Self) -> Self {
		x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
	}

	fn gamma1(x: Self) -> Self {
		x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
	}

	fn from_be_bytes(bytes: &[u8]) -> Self {
		u32::from_be_bytes(bytes.try_into().unwrap())
	}

	fn wrapping_add(self, rhs: Self) -> Self {
		self.wrapping_add(rhs)
	}

	fn from_u64_vec(slice: Vec<u64>) -> Vec<Self> {
		slice.into_iter().map(|x| x as u32).collect()
	}
}

impl Word for u64 {
	fn ch(e: Self, f: Self, g: Self) -> Self {
		(e & f) ^ (!e & g)
	}

	fn maj(a: Self, b: Self, c: Self) -> Self {
		(a & b) ^ (a & c) ^ (b & c)
	}

	fn sigma0(a: Self) -> Self {
		a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39)
	}

	fn sigma1(e: Self) -> Self {
		e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41)
	}

	fn gamma0(x: Self) -> Self {
		x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7)
	}

	fn gamma1(x: Self) -> Self {
		x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6)
	}

	fn from_be_bytes(bytes: &[u8]) -> Self {
		u64::from_be_bytes(bytes.try_into().unwrap())
	}

	fn wrapping_add(self, rhs: Self) -> Self {
		self.wrapping_add(rhs)
	}

	fn from_u64_vec(slice: Vec<u64>) -> Vec<Self> {
		slice
	}
}

#[derive(Debug, PartialEq, Clone)]
pub struct HashResult<W: Word> {
	pub hash: Box<[W]>,
	pub states: Vec<State<W>>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct State<W: Word> {
	pub i: u8,
	pub w: W,
	pub a: W,
	pub e: W,
}

impl<W: Word> BitDifferential for State<W> {
	fn bit_diff(self, other: Self) -> String {
		let a_delta = self.a.bit_diff(other.a);
		let e_delta = self.e.bit_diff(other.e);
		let w_delta = self.w.bit_diff(other.w);

		format!("{a_delta} | {e_delta} | {w_delta}")
	}
}

impl<W: Word> BitDifferential for Vec<State<W>> {
	fn bit_diff(self, other: Self) -> String {
		let padding = size_of::<W>() * 8;
		let mut output = String::new();

		// Append heading
		output += &format!(
			" i | {:^padding$} | {:^padding$} | {:^padding$}\n",
			"ΔAᵢ", "ΔEᵢ", "ΔWᵢ"
		);

		// Append differential for each compression round
		for i in 0..self.len() {
			let diff = self[i].clone().bit_diff(other[i].clone());
			output += &format!("{i:2} | {diff}\n");
		}

		output.shrink_to_fit();
		output
	}
}

impl<W: Word> std::fmt::Display for HashResult<W> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		let word_size_bytes = size_of::<W>();
		let width = word_size_bytes * 2;

		for word in self.hash.iter() {
			write!(f, "{word:0width$x} ")?;
		}
		Ok(())
	}
}

#[derive(thiserror::Error, Debug, PartialEq, Clone)]
pub enum HashError {
	#[error("requested rounds {requested} exceeds maximum rounds {maximum} for hash function")]
	TooManyRounds {
		requested: u8,
		maximum: u8,
	},
	#[error("failed to convert message bytes to blocks")]
	ByteToBlockConversionFailed
}

pub struct Bits(usize);

impl Bits {
	pub fn bits(&self) -> usize {
		self.0
	}

	pub fn bytes(&self) -> usize {
		(self.0 + 7) / 8
	}
}

#[cfg_attr(feature = "benchmarking", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum HashFunction {
	SHA224,
	SHA256,
	SHA512,
}

impl Display for HashFunction {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			HashFunction::SHA224 => f.write_str("SHA224"),
			HashFunction::SHA256 => f.write_str("SHA256"),
			HashFunction::SHA512 => f.write_str("SHA512"),
		}
	}
}

impl HashFunction {
	pub fn max_rounds(&self) -> u8 {
		use HashFunction::*;
		match self {
			SHA224 | SHA256 => 64,
			SHA512 => 80,
		}
	}

	pub fn length_size(&self) -> Bits {
		use HashFunction::*;
		match self {
			SHA224 | SHA256 => Bits(64),
			SHA512 => Bits(128),
		}
	}

	pub fn block_size(&self) -> Bits {
		use HashFunction::*;
		match self {
			SHA224 | SHA256 => Bits(512),
			SHA512 => Bits(1024),
		}
	}

	pub fn word_size(&self) -> Bits {
		use HashFunction::*;
		match self {
			SHA224 | SHA256 => Bits(32),
			SHA512 => Bits(64),
		}
	}

	pub fn truncate_to_length(&self) -> Option<usize> {
		use HashFunction::*;
		match self {
			SHA224 => Some(7),
			_ => None,
		}
	}

	/// Validates number of compression rounds.
	/// Returns error if rounds exceed max_rounds of given hash function.
	///
	/// # Arguments
	///
	/// * `rounds`: Number of compression rounds
	/// * `hash_function`: Hash function to validate against
	///
	/// # Returns
	/// `Result<(), HashError>`
	pub fn validate_rounds(&self, rounds: u8) -> Result<(), HashError> {
		let max_rounds = self.max_rounds();
		if rounds > max_rounds {
			return Err(HashError::TooManyRounds {
				requested: rounds,
				maximum: max_rounds,
			});
		}

		Ok(())
	}

	/// Retrieves constant K
	pub fn get_constant(&self) -> Vec<u64> {
		use HashFunction::*;
		match self {
			SHA224 | SHA256 => vec![
				0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
				0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
				0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
				0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
				0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
				0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
				0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
				0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
				0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
				0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
				0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
				0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
				0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
				0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
				0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
				0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
			],
			SHA512 => vec![
				0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
				0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
				0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
				0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
				0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
				0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
				0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
				0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
				0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
				0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
				0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
				0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
				0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
				0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
				0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
				0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
				0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
				0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
				0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
				0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
			],
		}
	}
}

#[cfg(test)]
mod tests {
	use super::{Bits, Word};

	#[test]
	fn test_word_ch() {
		let e = 20u32;
		let f = 40u32;
		let g = 60u32;

		assert_eq!(Word::ch(e, f, g), 40);

		let e = 20u64;
		let f = 40u64;
		let g = 60u64;

		assert_eq!(Word::ch(e, f, g), 40);
	}

	#[test]
	fn test_word_maj() {
		let a = 20u32;
		let b = 40u32;
		let c = 60u32;

		assert_eq!(Word::maj(a, b, c), 60);

		let a = 20u64;
		let b = 40u64;
		let c = 60u64;

		assert_eq!(Word::maj(a, b, c), 60);
	}

	#[test]
	fn test_word_sigma0() {
		assert_eq!(Word::sigma0(1u32), 1074267136);
		assert_eq!(Word::sigma0(1u64), 69826772992);
	}

	#[test]
	fn test_word_sigma1() {
		assert_eq!(Word::sigma1(1u32), 69206144);
		assert_eq!(Word::sigma1(1u64), 1196268659408896);
	}

	#[test]
	fn test_word_gamma0() {
		assert_eq!(Word::gamma0(1u32), 33570816);
		assert_eq!(Word::gamma0(1u64), 9295429630892703744);
	}

	#[test]
	fn test_word_gamma1() {
		assert_eq!(Word::gamma1(1u32), 40960);
		assert_eq!(Word::gamma1(1u64), 35184372088840);
	}

	#[test]
	fn test_word_from_be_bytes() {
		assert_eq!(<u32 as Word>::from_be_bytes(&8u32.to_be_bytes()), 8);
		assert_eq!(<u64 as Word>::from_be_bytes(&8u64.to_be_bytes()), 8);
	}

	#[test]
	fn test_word_wrapping_add() {
		assert_eq!(Word::wrapping_add(1u32, 2u32), 3);
		assert_eq!(Word::wrapping_add(1u64, 2u64), 3);

		assert_eq!(Word::wrapping_add(u32::MAX,2), 1);
		assert_eq!(Word::wrapping_add(u64::MAX, 2), 1);
	}

	#[test]
	fn test_bits_as_bits() {
		assert_eq!(Bits(8).bits(), 8);
	}

	#[test]
	fn test_bits_as_bytes() {
		assert_eq!(Bits(8).bytes(), 1);
	}

	#[test]
	fn test_bits_as_bytes_non_padded() {
		assert_eq!(Bits(11).bytes(), 2);
	}
}
