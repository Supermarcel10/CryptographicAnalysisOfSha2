use std::fmt::{Display, Formatter};
use bitvec::field::BitField;
use bitvec::macros::internal::funty::{Integral, Unsigned};
use bitvec::prelude::{BitArray, BitStore, Msb0};


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
	pub fn new(value: T) -> Self {
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
		self.bits = !self.bits
	}
}
