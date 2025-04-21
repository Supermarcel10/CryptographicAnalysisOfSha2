#[cfg(test)]
mod tests {
	use crate::sha::{Sha, StartVector};
	use crate::sha::StartVector::IV;
	use crate::structs::hash_function::HashFunction::*;
	use crate::verification::bit_differential::BitDifferential;

	#[test]
	/// Example in Li et al. (p.17, Table 4)
	fn test_sha256_state_collision_table() {
		let cv = StartVector::from([
			0x02b19d5a_u32, 0x88e1df04, 0x5ea3c7b7, 0xf2f7d1a4,
			0x86cb1b1f_u32, 0xc8ee51a5, 0x1b4d0541, 0x651b92e7,
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

		let result_m = Sha::from_message_block(m.into(), SHA256, 39, cv)
			.unwrap()
			.execute()
			.unwrap();

		let result_m_prime = Sha::from_message_block(m_prime.into(), SHA256, 39, cv)
			.unwrap()
			.execute()
			.unwrap();

		println!("{}", result_m.states.bit_diff(result_m_prime.states));

		assert_eq!(*result_m.hash.0, expected);
		assert_eq!(*result_m.hash.0, *result_m_prime.hash.0);
	}

	#[test]
	/// Example in Li et al. (p.25, Table 8)
	fn test_sha512_state_collision_table() {
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

		let result_m = Sha::from_message_block(m.into(), SHA512, 28, IV)
			.unwrap()
			.execute()
			.unwrap();

		let result_m_prime = Sha::from_message_block(m_prime.into(), SHA512, 28, IV)
			.unwrap()
			.execute()
			.unwrap();

		println!("{}", result_m.states.bit_diff(result_m_prime.states));

		assert_eq!(*result_m.hash.0, expected);
		assert_eq!(*result_m.hash.0, *result_m_prime.hash.0);
	}

	#[test]
	/// Example in Li et al. (p.27, Table 10)
	fn test_sha224_state_collision_table() {
		let cv = StartVector::from([
			0x791c9c6b_u32, 0xbaa7f900, 0xf7c53298, 0x9073cbbd,
			0xc90690c5_u32, 0x5591553c, 0x43a5d984, 0xaf92402d,
		]);

		let cv_prime = StartVector::from([
			0x791c9c6b_u32, 0xbaa7f900, 0xf7c53298, 0x9073cbbd,
			0xc90690c5_u32, 0x5591553c, 0x43a5d984, 0xbf92402d,
		]);

		let m: [u32; 16] = [
			0xf41d61b4, 0xce033ba2, 0xdd1bc208, 0xa268189b,
			0xee6bda2c, 0x5ddbe94d, 0x9675bbd3, 0x32c1ba8a,
			0x7eba797d, 0x88b06a8f, 0x3bc3015c, 0xd36f38cc,
			0xcfcb88e0, 0x3c70f7f3, 0xfaa0c1fe, 0x35c62535,
		];

		let m_prime: [u32; 16] = [
			0xe41d61b4, 0xce033ba2, 0xdd1bc208, 0xa268189b,
			0xee6bda2c, 0x5ddbe94d, 0x9675bbd3, 0x32c1ba8a,
			0x7eba797d, 0x98b06a8f, 0x39e3055c, 0xc36f38cc,
			0xce4b002d, 0x3c74f1f3, 0xfaa0c1fe, 0x35c62535,
		];

		let expected: [u32; 7] = [
			0x9af50cac, 0xc165a72f, 0xb6f1c9f3, 0xef54bad9,
			0xaf0cfb1f, 0x57d357c9, 0xc6462616,
		];

		let result_m = Sha::from_message_block(m.into(), SHA224, 40, cv)
			.unwrap()
			.execute()
			.unwrap();

		let result_m_prime = Sha::from_message_block(m_prime.into(), SHA224, 40, cv_prime)
			.unwrap()
			.execute()
			.unwrap();

		println!("{}", result_m.states.bit_diff(result_m_prime.states));

		assert_eq!(*result_m.hash.0, expected);
		assert_eq!(*result_m.hash.0, *result_m_prime.hash.0);
	}
}
