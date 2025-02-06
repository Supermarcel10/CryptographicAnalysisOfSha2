use std::fmt::{Display, Formatter};
use bitvec::field::BitField;
use bitvec::macros::internal::funty::Unsigned;
use bitvec::prelude::{BitArray, BitStore, Msb0};


#[derive(Debug, Clone, Copy)]
pub struct ShaHash<T: Unsigned + BitStore> {
	message_block: [Word<T>; 16]
}

impl<T: Unsigned + BitStore> Display for MessageBlock<T> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		// write!(f, "{}", self.words.load::<T>())
		todo!();
	}
}

impl<T: Unsigned + BitStore> MessageBlock<T> {
	pub fn new() -> Self {
		// TODO: Construct a proper message block based on a starting hash
		MessageBlock {
			words: [Word::new(0); 16],
		}
	}
}

#[derive(Debug, Clone, Copy)]
pub struct Word<T: Unsigned + BitStore> {
	bits: BitArray<T, Msb0>
}

impl<T: Unsigned + BitStore> PartialEq for Word<T> {
	fn eq(&self, other: &Self) -> bool {
		self.bits == other.bits
	}
}

impl<T: Unsigned + BitStore> Display for Word<T> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.bits.load::<T>())
	}
}

impl<T: Unsigned + BitStore> Word<T> {
	fn new(value: T) -> Self {
		Word {
			bits: BitArray::<T, Msb0>::new(value),
		}
	}

	pub fn rotate_left(&mut self, by: usize) {
		self.bits.rotate_left(by);
	}

	pub fn rotate_right(&mut self, by: usize) {
		self.bits.rotate_right(by);
	}

	pub fn mod_add(&mut self, other: Word<T>) {
		let mut carry = false;

		for i in (0..self.bits.len()).rev() {
			let s_bit = self.bits[i];
			let o_bit = other.bits[i];

			let sum = s_bit ^ o_bit ^ carry;
			carry = (s_bit && o_bit)
				|| (s_bit && carry)
				|| (o_bit && carry);

			self.bits.set(i, sum);
		}
	}

	pub fn and(&mut self, other: Word<T>) {
		self.bits = self.bits & other.bits;
	}

	pub fn or(&mut self, other: Word<T>) {
		self.bits = self.bits | other.bits;
	}

	pub fn xor(&mut self, other: Word<T>) {
		self.bits = self.bits ^ other.bits;
	}

	pub fn not(&mut self) {
		self.bits = !self.bits;
	}

	pub fn load(&self) -> T {
		self.bits.load()
	}
}

#[cfg(test)]
mod tests {
	use super::Word;

	#[test]
	fn test_load() {
		let word = Word::new(7u8);
		assert_eq!(word.load(), 7); // 7 == 7
	}

	#[test]
	fn test_rotate_right() {
		let mut word = Word::new(0b0100u8);
		word.rotate_right(2);
		assert_eq!(word.load(), 0b0001);
	}

	#[test]
	fn test_rotate_right_overflow() {
		let mut word = Word::new(0b0001u8);
		word.rotate_right(1);
		assert_eq!(word.load(), 0b1000_0000);
	}

	#[test]
	fn test_rotate_left() {
		let mut word = Word::new(0b0001u8);
		word.rotate_left(1);

		assert_eq!(word.load(), 0b0010);
	}

	#[test]
	fn test_rotate_left_overflow() {
		let mut word = Word::new(0b1000_0000u8);
		word.rotate_left(1);

		assert_eq!(word.load(), 0b0001);
	}

	#[test]
	fn test_mod_add() {
		let mut word1 = Word::new(3u8);
		let word2 = Word::new(5u8);

		word1.mod_add(word2);
		assert_eq!(word1.load(), 8) // (3 + 5) % 255 = 8
	}

	#[test]
	fn test_mod_add_overflow() {
		let mut word1 = Word::new(255u8);
		let word2 = Word::new(5u8);

		word1.mod_add(word2);
		assert_eq!(word1.load(), 4) // (255 + 4) % 255 = 259 % 255 = 4
	}

	#[test]
	fn test_and() {
		let mut word1 = Word::new(0b0001_0101u8);
		let word2 = Word::new(0b0011u8);
		word1.and(word2);

		assert_eq!(word1.load(), 0b0001);
	}

	#[test]
	fn test_or() {
		let mut word1 = Word::new(0b0001_0101u8);
		let word2 = Word::new(0b0011u8);
		word1.or(word2);

		assert_eq!(word1.load(), 0b0001_0111);
	}

	#[test]
	fn test_xor() {
		let mut word1 = Word::new(0b0001_0101u8);
		let word2 = Word::new(0b0011u8);
		word1.xor(word2);

		assert_eq!(word1.load(), 0b0001_0110);
	}

	#[test]
	fn test_not() {
		let mut word = Word::new(0b0000_1111u8);
		word.not();

		assert_eq!(word.load(), 0b1111_0000);
	}
}
