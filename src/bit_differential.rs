#[derive(Debug, Eq, PartialEq)]
enum DiffType {
	INCREASE,
	DECREASE,
	EQUAL,
	FALSE,
	TRUE,
}

impl DiffType {
	fn represent(&self) -> char {
		match self {
			DiffType::INCREASE => 'n',
			DiffType::DECREASE => 'u',
			DiffType::EQUAL => '=',
			DiffType::FALSE => '0',
			DiffType::TRUE => '1',
		}
	}
}

pub trait BitDifferential {
	fn show_differential(self, other: Self) -> String;
}

macro_rules! impl_bit_differential_for {
    ($($t:ty),*) => {
        $(
            impl BitDifferential for $t {
                fn show_differential(self, other: Self) -> String {
					let size = size_of::<Self>() * 8;
					let mut s: String = String::with_capacity(size);

					for i in (0..size).rev() {
						let bit_self = (self >> i) & 1 == 1;
						let bit_other = (other >> i) & 1 == 1;

						let representation = match (bit_self, bit_other) {
							(false, true) => DiffType::INCREASE,
							(true, false) => DiffType::DECREASE,
							//? TODO: Figure out what the difference is between this and the below
							_ if bit_self == bit_other => DiffType::EQUAL,
							(false, false) => DiffType::FALSE,
							(true, true) => DiffType::TRUE,
						}.represent();

						s.push(representation);
					}

					s
				}
            }
        )*
    }
}

impl_bit_differential_for!(u8, u16,u32, u64, u128);

impl<T: BitDifferential + Copy, const N: usize> BitDifferential for [T; N] {
	fn show_differential(self, other: Self) -> String {
		self.into_iter()
			.zip(other)
			.map(|(s, o)| s.show_differential(o))
			.collect::<String>()
	}
}

impl<T: BitDifferential + Copy> BitDifferential for &[T] {
	fn show_differential(self, other: Self) -> String {
		self.into_iter()
			.zip(other)
			.map(|(s, o)| s.show_differential(*o))
			.collect::<String>()
	}
}

impl<T: BitDifferential + Copy> BitDifferential for Vec<T> {
	fn show_differential(self, other: Self) -> String {
		(&self[..]).show_differential(&other[..])
	}
}

#[cfg(test)]
mod test {
	use crate::bit_differential::BitDifferential;

	#[test]
	fn test_differential_same() {
		let a = 5u8;
		let b = 5u8;

		assert_eq!(a.show_differential(b), "========");
	}

	#[test]
	fn test_differential_different() {
		let a = 123u8;
		let b = 5u8;

		assert_eq!(a.show_differential(b), "=uuuunu=");
	}

	#[test]
	fn test_differential_slice() {
		let a = [2u8; 2];
		let b = [1, 3];
		assert_eq!(a.show_differential(b), "======un=======n");
	}

	#[test]
	fn test_differential_boxed_slice() {
		let a = Box::<[u8]>::from([2; 2]);
		let b = Box::<[u8]>::from([1, 3]);
		assert_eq!(a.show_differential(&b), "======un=======n");
	}

	#[test]
	fn test_differential_vec() {
		let a = Vec::from([2u8; 2]);
		let b = Vec::from([1, 3]);
		assert_eq!(a.show_differential(b), "======un=======n");
	}
}
