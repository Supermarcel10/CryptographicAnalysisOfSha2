pub struct Bits(pub usize);

impl Bits {
	pub fn bits(&self) -> usize {
		self.0
	}

	pub fn bytes(&self) -> usize {
		(self.0 + 7) / 8
	}
}

#[cfg(test)]
mod tests {
	use super::Bits;

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
