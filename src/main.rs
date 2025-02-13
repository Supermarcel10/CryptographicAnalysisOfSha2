use crate::sha::sha::{sha256, sha512};

mod structs;
mod heuristics;
mod sha;

fn main() {
	let message = b"abc";
	let hash256_full = sha256(message, 64);
	println!("SHA256(abc) [64 rounds]: {:02x?}", hash256_full);

	let hash256_4 = sha256(message, 4);
	println!("SHA256(abc) [4 rounds]: {:02x?}", hash256_4);

	let hash512_full = sha512(message, 80);
	println!("SHA512(abc) [80 rounds]: {:02x?}", hash512_full);

	let hash512_4 = sha512(message, 4);
	println!("SHA512(abc) [4 rounds]: {:02x?}", hash512_4);
}
