use crate::sha::sha::Hash::{SHA256, SHA512};

// TODO: Generalise SHA implementation
// TODO: Utilise structs and bitvec::bitarray to simplify further

#[derive(Debug, Clone, Copy)]
enum Hash {
	SHA256,
	SHA512,
}

#[derive(Debug)]
struct HashParams {
	pub block_size: usize,
	pub len_size: usize,
}

impl Hash {
	pub fn params(self) -> HashParams {
		match self {
			SHA256 => HashParams { block_size: 64, len_size: 8 },
			SHA512 => HashParams { block_size: 128, len_size: 16 },
		}
	}
}

pub fn sha256(message: &[u8], rounds: usize) -> [u8; 32] {
	let padded = pad(message, SHA256);

	// SHA-256 initial hash values
	use super::constants::sha256::*;
	let (mut h0, mut h1, mut h2, mut h3, mut h4, mut h5, mut h6, mut h7) =
		(H0, H1, H2, H3, H4, H5, H6, H7);

	// Process each 512-bit block
	for chunk in padded.chunks(64) {
		let mut w = [0u32; 64];

		for (i, word_bytes) in chunk.chunks(4).enumerate().take(16) {
			w[i] = u32::from_be_bytes(word_bytes.try_into().unwrap());
		}

		for i in 16..64 {
			let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
			let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
			w[i] = w[i - 16]
				.wrapping_add(s0)
				.wrapping_add(w[i - 7])
				.wrapping_add(s1);
		}

		let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) =
			(h0, h1, h2, h3, h4, h5, h6, h7);

		let effective_rounds = rounds.min(64);
		for i in 0..effective_rounds {
			let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
			let ch = (e & f) ^ ((!e) & g);
			let temp1 = h
				.wrapping_add(s1)
				.wrapping_add(ch)
				.wrapping_add(K[i])
				.wrapping_add(w[i]);
			let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
			let maj = (a & b) ^ (a & c) ^ (b & c);
			let temp2 = s0.wrapping_add(maj);

			h = g;
			g = f;
			f = e;
			e = d.wrapping_add(temp1);
			d = c;
			c = b;
			b = a;
			a = temp1.wrapping_add(temp2);
		}

		h0 = h0.wrapping_add(a);
		h1 = h1.wrapping_add(b);
		h2 = h2.wrapping_add(c);
		h3 = h3.wrapping_add(d);
		h4 = h4.wrapping_add(e);
		h5 = h5.wrapping_add(f);
		h6 = h6.wrapping_add(g);
		h7 = h7.wrapping_add(h);
	}

	let mut digest = [0u8; 32];
	digest[0..4].copy_from_slice(&h0.to_be_bytes());
	digest[4..8].copy_from_slice(&h1.to_be_bytes());
	digest[8..12].copy_from_slice(&h2.to_be_bytes());
	digest[12..16].copy_from_slice(&h3.to_be_bytes());
	digest[16..20].copy_from_slice(&h4.to_be_bytes());
	digest[20..24].copy_from_slice(&h5.to_be_bytes());
	digest[24..28].copy_from_slice(&h6.to_be_bytes());
	digest[28..32].copy_from_slice(&h7.to_be_bytes());

	digest
}

pub fn sha512(message: &[u8], rounds: usize) -> [u8; 64] {
	let padded = pad(message, SHA512);

	// SHA-512 initial hash values
	use super::constants::sha512::*;
	let (mut h0, mut h1, mut h2, mut h3, mut h4, mut h5, mut h6, mut h7) =
		(H0, H1, H2, H3, H4, H5, H6, H7);

	// Process each 1024-bit block
	for chunk in padded.chunks(128) {
		let mut w = [0u64; 80];

		for (i, word_bytes) in chunk.chunks(8).enumerate().take(16) {
			w[i] = u64::from_be_bytes(word_bytes.try_into().unwrap());
		}

		for i in 16..80 {
			let s0 = w[i - 15].rotate_right(1) ^ w[i - 15].rotate_right(8) ^ (w[i - 15] >> 7);
			let s1 = w[i - 2].rotate_right(19) ^ w[i - 2].rotate_right(61) ^ (w[i - 2] >> 6);
			w[i] = w[i - 16]
				.wrapping_add(s0)
				.wrapping_add(w[i - 7])
				.wrapping_add(s1);
		}

		let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) =
			(h0, h1, h2, h3, h4, h5, h6, h7);

		let effective_rounds = rounds.min(80);
		for i in 0..effective_rounds {
			let s1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
			let ch = (e & f) ^ ((!e) & g);
			let temp1 = h
				.wrapping_add(s1)
				.wrapping_add(ch)
				.wrapping_add(K[i])
				.wrapping_add(w[i]);
			let s0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
			let maj = (a & b) ^ (a & c) ^ (b & c);
			let temp2 = s0.wrapping_add(maj);

			h = g;
			g = f;
			f = e;
			e = d.wrapping_add(temp1);
			d = c;
			c = b;
			b = a;
			a = temp1.wrapping_add(temp2);
		}

		h0 = h0.wrapping_add(a);
		h1 = h1.wrapping_add(b);
		h2 = h2.wrapping_add(c);
		h3 = h3.wrapping_add(d);
		h4 = h4.wrapping_add(e);
		h5 = h5.wrapping_add(f);
		h6 = h6.wrapping_add(g);
		h7 = h7.wrapping_add(h);
	}

	let mut digest = [0u8; 64];
	digest[0..8].copy_from_slice(&h0.to_be_bytes());
	digest[8..16].copy_from_slice(&h1.to_be_bytes());
	digest[16..24].copy_from_slice(&h2.to_be_bytes());
	digest[24..32].copy_from_slice(&h3.to_be_bytes());
	digest[32..40].copy_from_slice(&h4.to_be_bytes());
	digest[40..48].copy_from_slice(&h5.to_be_bytes());
	digest[48..56].copy_from_slice(&h6.to_be_bytes());
	digest[56..64].copy_from_slice(&h7.to_be_bytes());

	digest
}

fn pad(message: &[u8], hash_function: Hash) -> Vec<u8> {
	let params = hash_function.params();

	let mut padded = message.to_vec();
	padded.push(0x80);

	while padded.len() % params.block_size != (params.block_size - params.len_size) {
		padded.push(0);
	}

	let bit_len = (message.len() * 8) as u128;
	padded.extend_from_slice(&bit_len.to_be_bytes()[16 - params.len_size..]);

	padded
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	/// Using 64 rounds should match the standard SHA-256 for "abc".
	fn test_sha256_standard() {
		let hash = sha256(b"abc", 64);
		let expected = [
			0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
			0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
			0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
			0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
		];

		assert_eq!(hash, expected);
	}

	#[test]
	/// Using 80 rounds should match the standard SHA-512 for "abc".
	fn test_sha512_standard() {
		let hash = sha512(b"abc", 80);
		let expected = [
			0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba,
			0xcc, 0x41, 0x73, 0x49, 0xae, 0x20, 0x41, 0x31,
			0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9, 0x7e, 0xa2,
			0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a,
			0x21, 0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8,
			0x36, 0xba, 0x3c, 0x23, 0xa3, 0xfe, 0xeb, 0xbd,
			0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8, 0x0e,
			0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f,
		];

		assert_eq!(hash, expected);
	}
}
