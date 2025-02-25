use crate::sha::*;

mod heuristics;
mod sha;
mod structs;

fn main() {
	let message = "abc";
	let hash256_full = sha(message, HashFunction::SHA256, 64);
	match hash256_full {
		Ok(hash) => {
			println!("SHA256(abc) [64 rounds]: {:02x?}", hash);
			println!("{}", hash.data.len());
		},
		Err(err) => println!("{}", err),
	};

	let hash512_full = sha(message, HashFunction::SHA512, 80);
	match hash512_full {
		Ok(hash) => {
			println!("SHA512(abc) [80 rounds]: {:02x?}", hash);
			println!("{}", hash.data.len());
		},
		Err(err) => println!("{}", err),
	};
}
