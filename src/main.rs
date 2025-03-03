use crate::sha::HashFunction::SHA256;
use crate::sha::Sha;
use crate::sha::StartVector::CV;
use crate::verification::bit_differential::BitDifferential;

mod heuristics;
mod sha;
mod verification;

fn main() {
	// Example in Li et al. (p.17, Table 4)
	let cv = CV([
		0x02b19d5a, 0x88e1df04, 0x5ea3c7b7, 0xf2f7d1a4,
		0x86cb1b1f, 0xc8ee51a5, 0x1b4d0541, 0x651b92e7,
	]);

	let m: [u32; 16] = [
		0xc61d6de7, 0x755336e8, 0x5e61d618, 0x18036de6,
		0xa79f2f1d, 0xf2b44c7b, 0x4c0ef36b, 0xa85d45cf,
		0xf72b8c2f, 0x0def947c, 0xa0eab159, 0x8021370c,
		0x4b0d8011, 0x7aad07f6, 0x33cd6902, 0x3bad5d64,
	];

	let m_prime: [u32; 16] = [
		0xc61d6de7, 0x755336e8, 0x5e61d618, 0x18036de6,
		0xa79f2f1d, 0xf2b44c7b, 0x4c0ef36b, 0xa85d45cf,
		0xe72b8c2f, 0x0fcf907c, 0xb0eab159, 0x81a1bfc1,
		0x4b098611, 0x7aad07f6, 0x33cd6902, 0x3bad5d64,
	];

	let _expected: [u32; 8] = [
		0x431cadcd, 0xce6893bb, 0xd6c9689a, 0x334854e8,
		0x3baae1ab, 0x038a195a, 0xccf54a19, 0x1c40606d,
	];

	let result_m = Sha::<u32>::from_message_block(m, SHA256, 39, cv)
		.unwrap()
		.execute();

	let result_m_prime = Sha::<u32>::from_message_block(m_prime, SHA256, 39, cv)
		.unwrap()
		.execute();

	println!("{}", result_m.states.bit_diff(result_m_prime.states));
}
