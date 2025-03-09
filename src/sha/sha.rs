use std::cmp::PartialEq;
use crate::sha::HashError::ByteToBlockConversionFailed;
use crate::sha::structs::{HashError, HashFunction, HashResult, State, Word};

#[derive(Debug)]
pub struct Sha<W: Word> {
	/// Message blocks
	blocks: [W; 16],
	/// Current state of sha function
	state: [W; 8],
	/// Hash function to use
	hash_function: HashFunction,
	/// Number of compression rounds
	rounds: u8,
}

#[cfg_attr(feature = "benchmarking", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum StartVector<W: Word> {
	/// Initial Vector
	IV,
	/// Chaining Vector
	CV([W; 8])
}

impl<W: Word> Sha<W> {
	/// Construct an SHA digest from a string message.
	///
	/// # Arguments
	///
	/// * `message`: Message to hash
	/// * `hash_function`: Hash function to use
	/// * `rounds`: Number of compression rounds
	/// * `start_vector`: Vector to start with
	///
	/// # Returns
	/// `Result<Sha<W>, HashError>`
	///
	/// Returns SHA digest or HashError.
	///
	/// # Examples
	///
	/// ```
	/// let sha_digest = Sha::<u32>::from_string("abc", SHA256, 64, IV);
	/// ```
	pub fn from_string(
		message: &str,
		hash_function: HashFunction,
		rounds: u8,
		start_vector: StartVector<W>
	) -> Result<Self, HashError> {
		Self::validate_rounds(rounds, hash_function)?;

		let bytes = Self::pad_message(message.as_bytes(), hash_function);
		let blocks = Self::bytes_to_blocks(&bytes)?;

		let state = match start_vector {
			StartVector::IV => Self::get_initial_vector(hash_function),
			StartVector::CV(state) => state,
		};

		Ok(Sha {
			blocks,
			state,
			hash_function,
			rounds,
		})
	}

	/// Construct an SHA digest from a prepared padded message block.
	///
	/// # Arguments
	///
	/// * `blocks`: Message blocks to hash
	/// * `hash_function`: Hash function to use
	/// * `rounds`: Number of compression rounds
	/// * `start_vector`: Vector to start with
	///
	/// # Returns
	/// `Result<Sha<W>, HashError>`
	///
	/// Returns SHA digest or HashError.
	///
	/// # Examples
	///
	/// ```
	/// let message: [u32; 16] = [
	/// 	0xc61d6de7, 0x755336e8, 0x5e61d618, 0x18036de6,
	/// 	0xa79f2f1d, 0xf2b44c7b, 0x4c0ef36b, 0xa85d45cf,
	/// 	0xf72b8c2f, 0x0def947c, 0xa0eab159, 0x8021370c,
	/// 	0x4b0d8011, 0x7aad07f6, 0x33cd6902, 0x3bad5d64,
	/// ];
	///
	/// let sha_digest = Sha::<u32>::from_hash(message, SHA256, 64, IV);
	/// ```
	pub fn from_message_block(
		blocks: [W; 16],
		hash_function: HashFunction,
		rounds: u8,
		start_vector: StartVector<W>,
	) -> Result<Self, HashError> {
		Self::validate_rounds(rounds, hash_function)?;

		let state = match start_vector {
			StartVector::IV => Self::get_initial_vector(hash_function),
			StartVector::CV(state) => state,
		};

		Ok(Sha {
			blocks,
			state,
			hash_function,
			rounds,
		})
	}

	/// Executes the hashing and compression algorithm.
	///
	/// # Returns
	/// `HashResult<W>`
	///
	/// Returns HashResult of words.
	///
	/// # Examples
	///
	/// ```
	/// let sha_digest = Sha::<u32>::from_hash(message, SHA256, 64, IV)?;
	///
	/// let hash = sha_digest.execute();
	/// ```
	pub fn execute(mut self) -> HashResult<W> {
		let k = self.get_constant();
		let mut w = vec![W::default(); k.len()];
		let mut states = Vec::<State<W>>::with_capacity(self.rounds as usize);

		// Initialization of first 16 words with current block
		w[..16].copy_from_slice(&self.blocks);

		// Message schedule expansion
		for i in 16..self.rounds as usize {
			w[i] = w[i-16]
				.wrapping_add(W::gamma0(w[i-15]))
				.wrapping_add(w[i-7])
				.wrapping_add(W::gamma1(w[i-2]));
		}

		// Initialize working variables
		let mut working_vars = self.state.clone();

		// Compression loop
		for i in 0..self.rounds as usize {
			let t1 = working_vars[7]
				.wrapping_add(W::sigma1(working_vars[4]))
				.wrapping_add(W::ch(working_vars[4], working_vars[5], working_vars[6]))
				.wrapping_add(k[i])
				.wrapping_add(w[i]);

			let t2 = W::sigma0(working_vars[0])
				.wrapping_add(W::maj(working_vars[0], working_vars[1], working_vars[2]));

			// Rotate working variables
			working_vars.rotate_right(1);
			working_vars[0] = t1.wrapping_add(t2);
			working_vars[4] = working_vars[4].wrapping_add(t1);

			states.push(State {
				i: i as u8,
				w: w[i].clone(),
				a: working_vars[0],
				e: working_vars[4],
			});
		}

		// Update state
		for i in 0..8 {
			self.state[i] = self.state[i].wrapping_add(working_vars[i]);
		}

		// Truncate
		let truncate_to_length = self.hash_function
			.truncate_to_length()
			.or(Some(self.state.len()))
			.unwrap();

		let hash = Box::from(&self.state[..truncate_to_length]);

		HashResult {
			hash,
			states,
		}
	}

	/// Validates number of compression rounds.
	/// Returns error if rounds exceed max_rounds of given hash function.
	///
	/// # Arguments
	///
	/// * `rounds`: Number of compression rounds
	/// * `hash_function`: Hash function to validate against
	///
	/// # Returns
	/// `Result<(), HashError>`
	fn validate_rounds(rounds: u8, hash_function: HashFunction) -> Result<(), HashError> {
		let max_rounds = hash_function.max_rounds();
		if rounds > max_rounds {
			return Err(HashError::TooManyRounds {
				requested: rounds,
				maximum: max_rounds,
			});
		}

		Ok(())
	}

	/// Pads the given message with SHA2 rules.
	/// Returns vector of padded message, with block size length of given hash function.
	///
	/// # Arguments
	///
	/// * `message`: Message to pad
	/// * `hash_function`: Hash function to pad for
	///
	/// # Returns
	/// `Vec<u8, Global>`
	///
	/// # Examples
	///
	/// ```
	/// let message = b"abc";
	/// let padded_message = Self::pad_message(message, HashFunction::SHA256);
	/// ```
	fn pad_message(message: &[u8], hash_function: HashFunction) -> Vec<u8> {
		// Example message "ABC" (3 char, 24b) for SHA 256
		// | Original Message | Single 1 | Padding (0's)             | Length (64b)          |
		// |------------------|----------|---------------------------|-----------------------|
		// | 24b              |    1b    | 423b of zero-padding      | 64b representing "24" |

		let block_size_bytes = hash_function.block_size().bytes();
		let length_size_bytes = hash_function.length_size().bytes();

		let mut padded = message.to_vec();
		padded.push(0x80);  // '1' bit

		// Calculate padding zeros
		let needed = block_size_bytes - ((padded.len() + length_size_bytes) % block_size_bytes);
		padded.extend(vec![0u8; needed]);

		// Append original bit length
		let bit_len = (message.len() as u128) * 8;
		padded.extend(&bit_len.to_be_bytes()[16 - length_size_bytes..]);

		padded
	}

	/// Converts padded byte message to blocks.
	///
	/// # Arguments
	///
	/// * `bytes`: padded byte message
	///
	/// # Returns
	/// `Result<[W; 16], HashError>` 16 blocks of words
	fn bytes_to_blocks(bytes: &[u8]) -> Result<[W; 16], HashError> {
		let word_size_bytes = size_of::<W>();

		let value: Result<[W; 16], _> = bytes.chunks_exact(word_size_bytes)
			.map(|chunk| W::from_be_bytes(chunk))
			.collect::<Vec<_>>()
			.try_into();

		if value.is_err() {
			return Err(ByteToBlockConversionFailed)
		}

		Ok(value.unwrap())
	}

	/// Retrieves initial vector (IV), often referred to as H variables
	fn get_initial_vector(hash_function: HashFunction) -> [W; 8] {
		let vec = match hash_function {
			HashFunction::SHA224 => W::from_u64_vec(vec![
				0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
				0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4,
			]),
			HashFunction::SHA256 => W::from_u64_vec(vec![
				0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
				0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
			]),
			HashFunction::SHA512 => W::from_u64_vec(vec![
				0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
				0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
			]),
		};

		vec.try_into().expect("Failed to convert initial vector; vector size mismatch!")
	}

	/// Retrieves constant K
	fn get_constant(&self) -> Vec<W> {
		use HashFunction::*;
		match self.hash_function {
			SHA224 | SHA256 => W::from_u64_vec(vec![
				0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
				0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
				0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
				0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
				0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
				0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
				0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
				0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
				0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
				0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
				0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
				0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
				0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
				0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
				0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
				0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
			]),
			SHA512 => W::from_u64_vec(vec![
				0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
				0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
				0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
				0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
				0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
				0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
				0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
				0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
				0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
				0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
				0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
				0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
				0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
				0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
				0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
				0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
				0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
				0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
				0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
				0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
			]),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::HashFunction::{SHA224, SHA256, SHA512};
	use super::StartVector::*;
	use super::*;

	const MESSAGE: &str = "abc";

	#[test]
	fn test_padding() {
		// MESSAGE "abc" (3 char, 24b) for SHA 256
		// | Original Message | Single 1 | Padding (0's)             | Length (64b)          |
		// |------------------|----------|---------------------------|-----------------------|
		// | 24b              |    1b    | 423b of zero-padding      | 64b representing "24" |

		let expected = vec![
			// Original message characters
			97, 98, 99,
			// Single 1 as Big Endian
			128, // Binary 1000 0000
			// Padding of 0s
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0,
			// Lenth of message in bits
			24
		];

		assert_eq!(Sha::<u32>::pad_message(MESSAGE.as_bytes(), SHA256), expected);
	}

	#[test]
	/// Using 64 rounds should match the standard SHA-224 for "abc".
	fn test_sha224_correctness() {
		let result = Sha::<u32>::from_string(MESSAGE, SHA224, 64, IV)
			.unwrap()
			.execute();

		let expected = [
			0x23097d22, 0x3405d822, 0x8642a477, 0xbda255b3,
			0x2aadbce4, 0xbda0b3f7, 0xe36c9da7,
		];

		assert_eq!(*result.hash, expected);
	}

	#[test]
	/// Using 64 rounds should match the standard SHA-256 for "abc".
	fn test_sha256_correctness() {
		let result = Sha::<u32>::from_string(MESSAGE, SHA256, 64, IV)
			.unwrap()
			.execute();

		let expected = [
			0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
			0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad,
		];

		assert_eq!(*result.hash, expected);
	}

	#[test]
	/// Using 80 rounds should match the standard SHA-512 for "abc".
	fn test_sha512_correctness() {
		let result = Sha::<u64>::from_string(MESSAGE, SHA512, 80, IV)
			.unwrap()
			.execute();

		let expected = [
			0xddaf35a193617aba, 0xcc417349ae204131, 0x12e6fa4e89a97ea2, 0x0a9eeee64b55d39a,
			0x2192992a274fc1a8, 0x36ba3c23a3feebbd, 0x454d4423643ce80e, 0x2a9ac94fa54ca49f,
		];

		assert_eq!(*result.hash, expected);
	}

	#[test]
	fn test_sha256_round_difference() {
		let result_32r = Sha::<u32>::from_string(MESSAGE, SHA256, 32, IV)
			.unwrap()
			.execute();

		let result_64r = Sha::<u32>::from_string(MESSAGE, SHA256, 64, IV)
			.unwrap()
			.execute();

		assert_ne!(result_32r, result_64r);
	}

	#[test]
	fn test_sha512_round_difference() {
		let result_40r = Sha::<u64>::from_string(MESSAGE, SHA512, 40, IV)
			.unwrap()
			.execute();

		let result_80r = Sha::<u64>::from_string(MESSAGE, SHA512, 80, IV)
			.unwrap()
			.execute();

		assert_ne!(result_40r, result_80r);
	}

	#[test]
	/// Example in Li et al. (p.17, Table 5)
	fn test_single_cv_collision_sha256() {
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

		let expected: [u32; 8] = [
			0x431cadcd, 0xce6893bb, 0xd6c9689a, 0x334854e8,
			0x3baae1ab, 0x038a195a, 0xccf54a19, 0x1c40606d,
		];

		let result_m = Sha::<u32>::from_message_block(m, SHA256, 39, cv)
			.unwrap()
			.execute();

		let result_m_prime = Sha::<u32>::from_message_block(m_prime, SHA256, 39, cv)
			.unwrap()
			.execute();

		assert_eq!(*result_m.hash, expected);
		assert_eq!(*result_m.hash, *result_m_prime.hash);
	}

	#[test]
	/// Example in Li et al. (p.26, Table 9)
	fn test_single_cv_collision_sha512() {
		let m: [u64; 16] = [
			0x1f736d69a0368ef6, 0x7277e5081ad1c198, 0xe953a3cdc4cbe577, 0xbd05f6a203b2f75f,
			0xdd18b3e39f563fca, 0xcad0a5bb69049fcd, 0x4d0dd2a06e2efdc0, 0x86db19c26fc2e1cf,
			0x0184949e92cdd314, 0x82fb3c1420112000, 0xe4930d9b8295ab26, 0x5500d3a2f30a3402,
			0x26f0aa8790cb1813, 0xa9c09c5c5015bc0d, 0x53892c5a64e94edb, 0x8e60d500013a1932,
		];

		let m_prime: [u64; 16] = [
			0x1f736d69a0368ef6, 0x7277e5081ad1c198, 0xe953a3cdc4cbe577, 0xbd05f6a203b2f75f,
			0xdd18b3e39f563fca, 0xcad0a5bb69049fcd, 0x4d0dd2a06e2efdc0, 0x86db19c26fc2e1cf,
			0x037a8f464c0bb995, 0x83033bd41e111fff, 0xe4930d9b8295ab26, 0x5500d3a2f30a3402,
			0x26f0aa8790cb1813, 0xa9809e5c4015bc45, 0x53892c5a64e94edb, 0x8e60d500013a1932,
		];

		let expected: [u64; 8] = [
			0xdceb3d88adf54bd2, 0x966c4cb1ab0cf400, 0x01e701fdf10ab603, 0x796d6e5028a5e89a,
			0xf29a7517b216c09f, 0x46dbae73b1db8cce, 0x8ea44d45041010ea, 0x26a7a6b902f2632f,
		];

		let result_m = Sha::<u64>::from_message_block(m, SHA512, 28, IV)
			.unwrap()
			.execute();

		let result_m_prime = Sha::<u64>::from_message_block(m_prime, SHA512, 28, IV)
			.unwrap()
			.execute();

		assert_eq!(*result_m.hash, expected);
		assert_eq!(*result_m.hash, *result_m_prime.hash);
	}

	#[test]
	/// Example in Li et al. (p.27, Table 10)
	fn test_dual_cv_collision_sha224() {
		let cv = CV([
			0x791c9c6b, 0xbaa7f900, 0xf7c53298, 0x9073cbbd,
			0xc90690c5, 0x5591553c, 0x43a5d984, 0xaf92402d,
		]);

		let cv_prime = CV([
			0x791c9c6b, 0xbaa7f900, 0xf7c53298, 0x9073cbbd,
			0xc90690c5, 0x5591553c, 0x43a5d984, 0xbf92402d,
		]);

		let m = [
			0xf41d61b4, 0xce033ba2, 0xdd1bc208, 0xa268189b,
			0xee6bda2c, 0x5ddbe94d, 0x9675bbd3, 0x32c1ba8a,
			0x7eba797d, 0x88b06a8f, 0x3bc3015c, 0xd36f38cc,
			0xcfcb88e0, 0x3c70f7f3, 0xfaa0c1fe, 0x35c62535,
		];

		let m_prime = [
			0xe41d61b4, 0xce033ba2, 0xdd1bc208, 0xa268189b,
			0xee6bda2c, 0x5ddbe94d, 0x9675bbd3, 0x32c1ba8a,
			0x7eba797d, 0x98b06a8f, 0x39e3055c, 0xc36f38cc,
			0xce4b002d, 0x3c74f1f3, 0xfaa0c1fe, 0x35c62535,
		];

		let expected = [
			0x9af50cac, 0xc165a72f, 0xb6f1c9f3, 0xef54bad9,
			0xaf0cfb1f, 0x57d357c9, 0xc6462616,
		];

		let result_m = Sha::<u32>::from_message_block(m, SHA224, 40, cv)
			.unwrap()
			.execute();

		let result_m_prime = Sha::<u32>::from_message_block(m_prime, SHA224, 40, cv_prime)
			.unwrap()
			.execute();

		assert_eq!(*result_m.hash, expected);
		assert_eq!(*result_m.hash, *result_m_prime.hash);
	}

	#[test]
	fn test_too_many_rounds() {
		let result = Sha::<u32>::from_string(MESSAGE, SHA224, 65, IV);
		assert!(matches!(result, Err(HashError::TooManyRounds { .. })));

		let result = Sha::<u32>::from_string(MESSAGE, SHA256, 65, IV);
		assert!(matches!(result, Err(HashError::TooManyRounds { .. })));

		let result = Sha::<u32>::from_string(MESSAGE, SHA512, 81, IV);
		assert!(matches!(result, Err(HashError::TooManyRounds { .. })));
	}
}
