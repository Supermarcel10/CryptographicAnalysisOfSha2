// Math implemented as defined on Wikipedia https://en.wikipedia.org/wiki/SHA-2
pub trait Word: Copy + Default {
	fn ch(e: Self, f: Self, g: Self) -> Self;
	fn maj(a: Self, b: Self, c: Self) -> Self;
	fn sigma0(a: Self) -> Self;
	fn sigma1(e: Self) -> Self;
	fn gamma0(x: Self) -> Self;
	fn gamma1(x: Self) -> Self;
	fn from_be_bytes(bytes: &[u8]) -> Self;
	fn wrapping_add(self, rhs: Self) -> Self;
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
}

#[derive(Debug)]
pub struct HashResult {
	pub data: Box<[u8]>,
}

impl FromIterator<u8> for HashResult {
	fn from_iter<T: IntoIterator<Item=u8>>(iter: T) -> Self {
		let data = iter.into_iter().collect::<Box<_>>().into();
		HashResult { data }
	}
}

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum HashError {
	#[error("requested rounds {requested} exceeds maximum rounds {maximum} for hash function")]
	TooManyRounds {
		requested: u32,
		maximum: u32,
	},
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

#[derive(Debug, Clone, Copy)]
pub enum HashFunction {
	SHA256,
	SHA512,
}

impl HashFunction {
	pub fn max_rounds(&self) -> u32 {
		match self {
			HashFunction::SHA256 => 64,
			HashFunction::SHA512 => 80,
		}
	}

	pub fn length_size(&self) -> Bits {
		match self {
			HashFunction::SHA256 => Bits(64),
			HashFunction::SHA512 => Bits(128),
		}
	}

	pub fn chunk_size(&self) -> Bits {
		match self {
			HashFunction::SHA256 => Bits(64),
			HashFunction::SHA512 => Bits(128),
		}
	}

	pub fn block_size(&self) -> Bits {
		match self {
			HashFunction::SHA256 => Bits(512),
			HashFunction::SHA512 => Bits(1024),
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
