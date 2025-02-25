use crate::bit_differential::BitDifferential;
use crate::sha::*;

mod heuristics;
mod sha;
mod structs;
mod bit_differential;

fn main() {
	let message = "abc";
	let hash256_full = sha(message, HashFunction::SHA256, 64);
	match hash256_full {
		Ok(hash) => {
			println!("SHA256(abc) [64 rounds]: {:02x?}", hash);
			println!("{}", hash.len());
		},
		Err(err) => println!("{}", err),
	};
}
