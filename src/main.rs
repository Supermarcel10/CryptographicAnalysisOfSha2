use crate::sha::*;

mod heuristics;
mod sha;
mod structs;

fn main() {
	let message = "abc";
	let hash256_full = sha(message, HashFunction::SHA256, 64);
	println!("SHA256(abc) [64 rounds]: {:02x?}", hash256_full.unwrap());

	let hash256_4 = sha(message, HashFunction::SHA256, 4);
	println!("SHA256(abc) [4 rounds]: {:02x?}", hash256_4.unwrap());

	let hash512_full = sha(message, HashFunction::SHA512, 80);
	println!("SHA512(abc) [80 rounds]: {:02x?}", hash512_full.unwrap());

	let hash512_4 = sha(message, HashFunction::SHA512, 4);
	println!("SHA512(abc) [4 rounds]: {:02x?}", hash512_4.unwrap());

	let hash512_90 = sha(message, HashFunction::SHA512, 90);
	match hash512_90 {
		Ok(hash512_90) => println!("SHA512(abc) [90 rounds]: {:02x?}", hash512_90),
		Err(err) => println!("SHA512(abc) [90 rounds]: {}", err),
	};

	let message = String::from("abc");
	let hashed_sha256 = sha(&message, HashFunction::SHA256, 4);
	println!("My hash is {:?}!", hashed_sha256.unwrap());
}
