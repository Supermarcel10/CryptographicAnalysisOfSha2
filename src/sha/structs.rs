use std::fmt::{Display, Formatter, LowerHex};
use std::num::ParseIntError;
use crate::structs::hash_function::HashFunction;
use crate::verification::bit_differential::BitDifferential;

#[derive(thiserror::Error, Debug, PartialEq, Clone)]
pub enum HashError {
	#[error("requested rounds {requested} exceeds maximum rounds {maximum} for hash function")]
	TooManyRounds {
		requested: u8,
		maximum: u8,
	},
	#[error("failed to convert bytes into valid word")]
	FailedToConvertBytes,
	#[error("attempted to {operation} on two different word sizes")]
	WordMismatch {
		operation: String,
	}
}

#[cfg_attr(feature = "benchmarking", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Word {
	W32(u32),
	W64(u64)
}

impl Display for Word {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Word::W32(w) => f.write_str(&format!("{w:08x}")),
			Word::W64(w) => f.write_str(&format!("{w:016x}"))
		}
	}
}

impl From<u32> for Word {
	fn from(value: u32) -> Self {
		Word::W32(value)
	}
}

impl From<u64> for Word {
	fn from(value: u64) -> Self {
		Word::W64(value)
	}
}

impl PartialEq<u32> for Word {
	fn eq(&self, other: &u32) -> bool {
		match self {
			Word::W32(s) => s == other,
			Word::W64(_) => false,
		}
	}

	fn ne(&self, other: &u32) -> bool {
		!self.eq(other)
	}
}

impl PartialEq<u64> for Word {
	fn eq(&self, other: &u64) -> bool {
		match self {
			Word::W32(_) => false,
			Word::W64(s) => s == other,
		}
	}

	fn ne(&self, other: &u64) -> bool {
		!self.eq(other)
	}
}

impl LowerHex for Word {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		match self {
			Word::W32(w) => f.write_str(&format!("{w:08x}")),
			Word::W64(w) => f.write_str(&format!("{w:016x}")),
		}?;

		Ok(())
	}
}

impl BitDifferential for Word {
	fn bit_diff(self, rhs: Self) -> String {
		use Word::*;
		match (self, rhs) {
			(W32(l), W32(r)) => l.bit_diff(r),
			(W64(l), W64(r)) => l.bit_diff(r),
			(_, _) => HashError::WordMismatch { operation: String::from("bit diff") }.to_string(),
		}
	}
}

impl Word {
	pub(super) fn ch(e: Self, f: Self, g: Self) -> Result<Self, HashError> {
		use Word::*;
		match (e, f, g) {
			(W32(e), W32(f), W32(g)) => Ok(W32((e & f) ^ (!e & g))),
			(W64(e), W64(f), W64(g)) => Ok(W64((e & f) ^ (!e & g))),
			(_, _, _) => Err(HashError::WordMismatch { operation: String::from("ch")}),
		}
	}

	pub(super) fn maj(a: Self, b: Self, c: Self) -> Result<Self, HashError> {
		use Word::*;
		match (a, b, c) {
			(W32(a), W32(b), W32(c)) => Ok(W32((a & b) ^ (a & c) ^ (b & c))),
			(W64(a), W64(b), W64(c)) => Ok(W64((a & b) ^ (a & c) ^ (b & c))),
			(_, _, _) => Err(HashError::WordMismatch { operation: String::from("maj")}),
		}
	}

	pub(super) fn sigma0(a: Self) -> Self {
		use Word::*;
		match a {
			W32(a) => W32(a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22)),
			W64(a) => W64(a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39)),
		}
	}

	pub(super) fn sigma1(e: Self) -> Self {
		use Word::*;
		match e {
			W32(e) => W32(e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25)),
			W64(e) => W64(e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41)),
		}
	}

	pub(super) fn gamma0(x: Self) -> Self {
		use Word::*;
		match x {
			W32(x) => W32(x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)),
			W64(x) => W64(x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7)),
		}
	}

	pub(super) fn gamma1(x: Self) -> Self {
		use Word::*;
		match x {
			W32(x) => W32(x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)),
			W64(x) => W64(x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6)),
		}
	}

	pub fn from_u32_vec(slice: Vec<u32>) -> Vec<Self> {
		slice.into_iter().map(|x| Word::W32(x)).collect()
	}

	pub fn from_u64_vec(slice: Vec<u64>) -> Vec<Self> {
		slice.into_iter().map(|x| Word::W64(x)).collect()
	}

	pub fn from_str_radix(
		src: &str,
		radix: u32,
		hash_function: HashFunction,
	) -> Result<Word, ParseIntError> {
		use HashFunction::*;
		match hash_function {
			SHA224 | SHA256 => Ok(Word::W32(u32::from_str_radix(src, radix)?)),
			SHA512 => Ok(Word::W64(u64::from_str_radix(src, radix)?)),
		}
	}

	pub(super) fn wrapping_add(self, rhs: Word) -> Result<Self, HashError> {
		match (self, rhs) {
			(Word::W32(l), Word::W32(r)) => Ok(Word::W32(l.wrapping_add(r))),
			(Word::W64(l), Word::W64(r)) => Ok(Word::W64(l.wrapping_add(r))),
			(_, _) => Err(HashError::WordMismatch { operation: String::from("wrapping add")})
		}
	}

	pub(super) fn from_be_bytes(bytes: &[u8]) -> Result<Self, HashError> {
		match bytes.len() {
			4 => Ok(Word::W32(u32::from_be_bytes(bytes.try_into().unwrap()))),
			8 => Ok(Word::W64(u64::from_be_bytes(bytes.try_into().unwrap()))),
			_ => Err(HashError::FailedToConvertBytes),
		}
	}

	pub fn to_be_bytes(self) -> Box<[u8]> {
		match self {
			Word::W32(w) => Box::from(w.to_be_bytes()),
			Word::W64(w) => Box::from(w.to_be_bytes()),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::Word;

	#[test]
	fn test_word_ch() {
		use Word::*;

		let e = W32(20);
		let f = W32(40);
		let g = W32(60);

		assert_eq!(Word::ch(e, f, g), Ok(W32(40)));

		let e = W64(20);
		let f = W64(40);
		let g = W64(60);

		assert_eq!(Word::ch(e, f, g), Ok(W64(40)));
	}

	#[test]
	fn test_word_maj() {
		use Word::*;

		let a = W32(20);
		let b = W32(40);
		let c = W32(60);

		assert_eq!(Word::maj(a, b, c).unwrap(), W32(60));

		let a = W64(20);
		let b = W64(40);
		let c = W64(60);

		assert_eq!(Word::maj(a, b, c).unwrap(), W64(60));
	}

	#[test]
	fn test_word_sigma0() {
		use Word::*;
		assert_eq!(Word::sigma0(W32(1)), W32(1074267136));
		assert_eq!(Word::sigma0(W64(1)), W64(69826772992));
	}

	#[test]
	fn test_word_sigma1() {
		use Word::*;
		assert_eq!(Word::sigma1(W32(1)), W32(69206144));
		assert_eq!(Word::sigma1(W64(1)), W64(1196268659408896));
	}

	#[test]
	fn test_word_gamma0() {
		use Word::*;
		assert_eq!(Word::gamma0(W32(1)), W32(33570816));
		assert_eq!(Word::gamma0(W64(1)), W64(9295429630892703744));
	}

	#[test]
	fn test_word_gamma1() {
		use Word::*;
		assert_eq!(Word::gamma1(W32(1)), W32(40960));
		assert_eq!(Word::gamma1(W64(1)), W64(35184372088840));
	}

	#[test]
	fn test_word_from_be_bytes() {
		use Word::*;

		assert_eq!(Word::from_be_bytes(&8u32.to_be_bytes()).unwrap(), W32(8));
		assert_eq!(Word::from_be_bytes(&8u64.to_be_bytes()).unwrap(), W64(8));
	}

	#[test]
	fn test_word_wrapping_add() {
		use Word::*;
		assert_eq!(Word::wrapping_add(W32(1), W32(2)).unwrap(), W32(3));
		assert_eq!(Word::wrapping_add(W64(1), W64(2)).unwrap(), W64(3));

		assert_eq!(Word::wrapping_add(W32(u32::MAX), W32(2)).unwrap(), W32(1));
		assert_eq!(Word::wrapping_add(W64(u64::MAX), W64(2)).unwrap(), W64(1));
	}
}
