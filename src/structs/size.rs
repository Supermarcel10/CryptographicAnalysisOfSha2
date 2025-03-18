/// Representation of a size, retrievable as bits or bytes.
/// Useful for distinguishing between bits and bytes in code.
pub struct Size(usize);

impl Size {
	/// Construct a size from a given number of bits.
	///
	/// # Arguments
	///
	/// `bits`: Number of bits to represent
	///
	/// # Returns
	/// `Size`
	///
	/// # Examples
	///
	/// ```
	/// let size = Bits::from_bits(8);
	/// ```
	pub fn from_bits(bits: usize) -> Self {
		Size(bits)
	}

	/// Construct a size from a given number of bytes.
	///
	/// # Arguments
	///
	/// `bytes`: Number of bytes to represent
	///
	/// # Returns
	/// `Size`
	///
	/// # Examples
	///
	/// ```
	/// let size = Bits::from_bytes(2);
	/// ```
	pub fn from_bytes(bytes: usize) -> Self {
		Size(bytes * 8)
	}

	/// Retreive the number of bits.
	///
	/// # Returns
	/// `usize`
	///
	/// # Examples
	///
	/// ```
	/// let size = Bits::from_bytes(2);
	/// println!("{}", size.bits()); // Outputs 16
	/// ```
	pub fn bits(&self) -> usize {
		self.0
	}

	/// Retreive the number of bytes.\
	/// The value will always be padded to the nearest full byte.
	///
	/// # Returns
	/// `usize`
	///
	/// # Examples
	///
	/// ```
	/// let size = Size::from_bits(8);
	/// println!("{}", size.bytes()); // Outputs 1
	/// ```
	///
	/// ```
	/// let size = Size::from_bits(12);
	/// println!("{}", size.bytes()); // Outputs 2
	/// ```
	pub fn bytes(&self) -> usize {
		(self.0 + 7) / 8
	}
}

#[cfg(test)]
mod tests {
	use super::Size;

	#[test]
	fn test_from_bits() {
		assert!(matches!(Size::from_bits(8), Size(8)));
		assert!(matches!(Size::from_bits(12), Size(12)));
	}

	#[test]
	fn test_from_bytes() {
		assert!(matches!(Size::from_bytes(1), Size(8)));
		assert!(matches!(Size::from_bytes(2), Size(16)));
	}

	#[test]
	fn test_bits() {
		assert_eq!(Size(8).bits(), 8);
	}

	#[test]
	fn test_bytes() {
		assert_eq!(Size(8).bytes(), 1);
	}

	#[test]
	fn test_non_full_bytes() {
		assert_eq!(Size(11).bytes(), 2);
	}
}
