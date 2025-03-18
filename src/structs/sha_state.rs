use crate::sha::Word;
use crate::verification::bit_differential::BitDifferential;

#[derive(Debug, PartialEq, Clone)]
pub struct ShaState<W: Word> {
	pub i: u8,
	pub w: W,
	pub a: W,
	pub e: W,
}

impl<W: Word> BitDifferential for ShaState<W> {
	fn bit_diff(self, other: Self) -> String {
		let a_delta = self.a.bit_diff(other.a);
		let e_delta = self.e.bit_diff(other.e);
		let w_delta = self.w.bit_diff(other.w);

		format!("{a_delta} | {e_delta} | {w_delta}")
	}
}

impl<W: Word> BitDifferential for Vec<ShaState<W>> {
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
