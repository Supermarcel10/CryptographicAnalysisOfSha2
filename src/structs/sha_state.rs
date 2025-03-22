use crate::sha::Word;
use crate::verification::bit_differential::BitDifferential;

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ShaState {
	pub i: u8,
	pub w: Word,
	pub a: Word,
	pub e: Word,
}

impl BitDifferential for ShaState {
	fn bit_diff(self, other: Self) -> String {
		let a_delta = self.a.bit_diff(other.a);
		let e_delta = self.e.bit_diff(other.e);
		let w_delta = self.w.bit_diff(other.w);

		format!("{a_delta} | {e_delta} | {w_delta}")
	}
}

impl BitDifferential for Vec<ShaState> {
	fn bit_diff(self, other: Self) -> String {
		let mut output = String::new();
		let padding = if let Some(state) = self.get(0) {
			match state.w {
				Word::W32(_) => 32,
				Word::W64(_) => 64,
			}
		} else { return output };

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
