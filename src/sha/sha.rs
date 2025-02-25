use crate::sha::structs::{HashError, HashFunction, Word};

/// # Arguments
///
/// * `state`: Initial hash values (H) (first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19)
/// * `block`: Initial block to process from padded message
/// * `rounds`: Number of compresison loop iterations
/// * `k`: Round constants (first 32 bits of the fractional parts of the cube roots of the first 64 primes 2..311)
///
/// # Returns
/// `Vec<T, Global>`
fn process_block<T: Word + Default>(
	mut state: Vec<T>,
	block: &[u8],
	rounds: u32,
	k: &[T],
) -> Vec<T> {
	let word_size = size_of::<T>();
	let mut w = vec![T::default(); k.len()];

	// Break chunk into words
	for i in 0..16 {
		w[i] = T::from_be_bytes(&block[i * word_size..(i + 1) * word_size]);
	}

	// Extend words
	for i in 16..k.len() {
		w[i] = w[i-16].wrapping_add(T::gamma0(w[i-15]))
			.wrapping_add(w[i-7])
			.wrapping_add(T::gamma1(w[i-2]));
	}

	// Initialize working variables
	let mut working_vars = state.clone();

	// Compression loop
	for i in 0..rounds as usize {
		let t1 = working_vars[7]
			.wrapping_add(T::sigma1(working_vars[4]))
			.wrapping_add(T::ch(working_vars[4], working_vars[5], working_vars[6]))
			.wrapping_add(k[i])
			.wrapping_add(w[i]);
		let t2 = T::sigma0(working_vars[0])
			.wrapping_add(T::maj(working_vars[0], working_vars[1], working_vars[2]));

		// Rotate working variables
		working_vars.rotate_right(1);
		working_vars[0] = t1.wrapping_add(t2);
		working_vars[4] = working_vars[4].wrapping_add(t1);
	}

	// Update state
	for i in 0..8 {
		state[i] = state[i].wrapping_add(working_vars[i]);
	}

	state
}

/// Generic sha function with control over number of rounds.
/// Returns vector of u8 hash or Error.
///
/// # Arguments
///
/// * `message`: The message to hash
/// * `hash_function`: The hashing function to use
/// * `rounds`: The number of rounds to hash for
///
/// # Returns
/// `Result<Vec<u8, Global>, HashError>`
///
/// # Examples
/// ## Valid call
/// ```
/// let message = String::from("abc");
/// let hashed_sha256 = sha(&message, HashFunction::SHA256, 4);
/// println!("My hash is {:?}!", hashed_sha256.unwrap());
/// // Outputs "My hash is [63, 90, 220, 205, 132, 42, 246, 44, 150, 217, 205, 31, 2, 186, 225, 7, 117, 238, 90, 207, 148, 46, 162, 119, 152, 82, 83, 52, 86, 11, 19, 59]!"
/// ```
///
/// ## Erroneous sha call
/// ```should_panic
/// let message = "abc";
/// let hashed_sha256 = sha(message, HashFunction::SHA256, 90);
/// println!("My hash is {:?}!", hashed_sha256.unwrap());
/// // Panics with HashError::TooManyRounds!
/// ```
pub fn sha(message: &str, hash_function: HashFunction, rounds: u32) -> Result<Vec<u8>, HashError> {
	// Validate rounds
	let max_rounds = hash_function.max_rounds();
	if rounds > max_rounds {
		return Err(HashError::TooManyRounds {
			requested: rounds,
			maximum: max_rounds,
		});
	}

	let padded_message = pad_message(message.as_bytes(), hash_function);

	let chunk_size_bits = hash_function.chunk_size().bits();

	match hash_function {
		HashFunction::SHA256 => {
			use super::constants::sha256::*;

			let mut state: Vec<u32> = H_INIT.to_vec();

			for chunk in padded_message.chunks(chunk_size_bits) {
				state = process_block(state, chunk, rounds, &K);
			}

			Ok(state.into_iter().flat_map(|x| x.to_be_bytes()).collect())
		},
		HashFunction::SHA512 => {
			use super::constants::sha512::*;

			let mut state: Vec<u64> = H_INIT.to_vec();

			for chunk in padded_message.chunks(chunk_size_bits) {
				state = process_block(state, chunk, rounds, &K);
			}

			Ok(state.into_iter().flat_map(|x| x.to_be_bytes()).collect())
		},
	}
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
/// let padded_message = pad_message(message, HashFunction::SHA256);
/// ```
fn pad_message(message: &[u8], hash_function: HashFunction) -> Vec<u8> {
	// Example message "ABC" (3 char, 24b) for SHA 256
	// | Original Message | Single 1 | Padding (0's)             | Length (64b)          |
	// |------------------|----------|---------------------------|-----------------------|
	// | 24b              |    1b    | 423b of zero-padding      | 64b representing "24" |

	let original_len_bits = (message.len() as u128) * 8;
	let block_size_bytes = hash_function.block_size().bytes();
	let length_size_bytes = hash_function.length_size().bytes();

	// Create a vector with the message followed by 1
	let mut padded = Vec::with_capacity(block_size_bytes);
	padded.extend_from_slice(message);
	padded.push(0x80);

	// Pad message with 0s
	padded.resize(block_size_bytes - length_size_bytes, 0);

	// Append length
	match hash_function {
		HashFunction::SHA256 => padded.extend_from_slice(&(original_len_bits as u64).to_be_bytes()),
		HashFunction::SHA512 => padded.extend_from_slice(&original_len_bits.to_be_bytes()),
	};

	padded
}

#[cfg(test)]
mod tests {
	use super::HashFunction::{SHA256, SHA512};
	use super::*;

	#[test]
	fn test_padding() {
		// Example message "ABC" (3 char, 24b) for SHA 256
		// | Original Message | Single 1 | Padding (0's)             | Length (64b)          |
		// |------------------|----------|---------------------------|-----------------------|
		// | 24b              |    1b    | 423b of zero-padding      | 64b representing "24" |

		let message = b"ABC";
		let expected = vec![
			// Original message for characters
			65, 66, 67,
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

		assert_eq!(pad_message(message, SHA256), expected);
	}

	#[test]
	/// Using 64 rounds should match the standard SHA-256 for "abc".
	fn test_sha256_correctness() {
		let message = "abc";
		let result = sha(message, SHA256, 64);

		let expected: [u8; 32] = [
			0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
			0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
			0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
			0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
		];

		assert_eq!(result.unwrap().into(), expected);
	}

	#[test]
	/// Using 80 rounds should match the standard SHA-512 for "abc".
	fn test_sha512_correctness() {
		let message = "abc";
		let result = sha(message, SHA512, 80);

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

		assert_eq!(result.unwrap().into(), expected);
	}

	#[test]
	fn test_sha256_round_difference() {
		let message = "abc";
		let result_32r = sha(message, SHA256, 32);
		let result_64r = sha(message, SHA256, 64);

		assert_ne!(result_32r, result_64r);
	}

	#[test]
	fn test_sha512_round_difference() {
		let message = "abc";
		let result_40r = sha(message, SHA512, 40);
		let result_80r = sha(message, SHA512, 80);

		assert_ne!(result_40r, result_80r);
	}

	#[test]
	fn test_too_many_rounds() {
		let message = "Hello, World!";
		let result = sha(message, SHA256, 65);
		assert!(matches!(result, Err(HashError::TooManyRounds { .. })));

		let result = sha(message, SHA512, 81);
		assert!(matches!(result, Err(HashError::TooManyRounds { .. })));
	}
}
