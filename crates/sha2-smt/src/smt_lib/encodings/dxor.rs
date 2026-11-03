#[cfg(test)]
mod tests {
	use sha2_core::structs::collision_type::CollisionType;
	use sha2_core::structs::hash_function::HashFunction;

	use crate::smt_lib::builder::SmtBuilder;
	use crate::smt_lib::encodings::encoding::{DsubEncoding, DxorEncoding, SmtEncoding};
	use crate::smt_lib::smt_retriever::EncodingType;

	fn dxor_builder(collision_type : CollisionType, rounds : u8) -> SmtBuilder {
		SmtBuilder {
			smt : String::new(),
			hash_function : HashFunction::SHA256,
			rounds,
			collision_type,
			encoding : EncodingType::DeltaXOR {
				simplified_maj_and_ch_functions : false,
				alternative_add : false
			}
		}
	}

	fn dsub_builder(collision_type : CollisionType, rounds : u8) -> SmtBuilder {
		SmtBuilder {
			smt : String::new(),
			hash_function : HashFunction::SHA256,
			rounds,
			collision_type,
			encoding : EncodingType::DeltaSub {
				simplified_maj_and_ch_functions : false,
				alternative_add : false
			}
		}
	}

	fn zeros() -> String {
		format!("#b{}", "0".repeat(32))
	}

	fn generated(collision_type : CollisionType, rounds : u8) -> String {
		let mut builder = dxor_builder(collision_type, rounds);
		DxorEncoding
			.generate(&mut builder)
			.expect("dxor generation must succeed without a solver");
		builder.smt
	}

	fn section_positions(smt : &str) -> Vec<usize> {
		[
			";; SETUP",
			";; TYPE",
			";; FUNCTIONS",
			";; CONSTANTS",
			";; MESSAGE EXPANSION",
			";; MESSAGE COMPRESSION",
			";; ASSERTIONS",
			";; GO!"
		]
		.iter()
		.map(|marker| {
			smt.find(marker)
				.expect("generated output missing a section")
		})
		.collect()
	}

	#[test]
	fn differentials_use_bvxor_and_never_bvsub() {
		for collision_type in [CollisionType::Standard, CollisionType::FreeStart] {
			let smt = generated(collision_type, 1);

			assert!(
				smt.contains("(define-fun delta_w0 () Word (bvxor m0_w0 m1_w0))"),
				"missing bvxor message differential for {collision_type:?}, got:\n{smt}"
			);
			assert!(
				smt.contains("(define-fun delta_a1 () Word (bvxor m0_a1 m1_a1))"),
				"missing bvxor working-variable differential for {collision_type:?}, got:\n{smt}"
			);
			assert!(
				smt.contains("(define-fun delta_hash0 () Word (bvxor m0_hash0 m1_hash0))"),
				"missing bvxor final-state differential for {collision_type:?}, got:\n{smt}"
			);
			assert!(
				!smt.contains("bvsub"),
				"dxor output must not mention bvsub for {collision_type:?}, got:\n{smt}"
			);
		}
	}

	#[test]
	fn standard_generation_asserts_message_difference_and_hash_equal() {
		let zeros = zeros();

		let one = generated(CollisionType::Standard, 1);
		assert!(
			one.contains("; Assert messages not the same"),
			"missing message-difference block, got:\n{one}"
		);
		assert!(
			one.contains(&format!("\t(distinct delta_w0 {zeros})\n")),
			"missing delta message-difference assertion, got:\n{one}"
		);
		assert!(
			one.contains("; Assert difference in output hash is none"),
			"missing hash-difference block, got:\n{one}"
		);
		assert!(
			one.contains(&format!("\t(= delta_hash0 {zeros})\n")),
			"missing hash-equality assertion, got:\n{one}"
		);
		assert!(
			one.contains("(check-sat)"),
			"missing check-sat, got:\n{one}"
		);
		assert!(
			section_positions(&one).is_sorted(),
			"sections out of order, got:\n{one}"
		);

		let two = generated(CollisionType::Standard, 2);
		assert!(
			two.contains("(define-fun delta_w1 () Word (bvxor m0_w1 m1_w1))"),
			"missing second-round message differential, got:\n{two}"
		);
		assert!(
			two.contains("(define-fun delta_a2 () Word (bvxor m0_a2 m1_a2))"),
			"missing second-round working-variable differential, got:\n{two}"
		);
		assert!(
			two.contains("(assert (or"),
			"two rounds must disjoin message differences, got:\n{two}"
		);
		assert!(
			section_positions(&two).is_sorted(),
			"sections out of order, got:\n{two}"
		);
	}

	#[test]
	fn free_start_generation_asserts_cv_difference() {
		let zeros = zeros();
		let smt = generated(CollisionType::FreeStart, 1);

		assert!(
			smt.contains("(define-fun delta_a0 () Word (bvxor m0_a0 m1_a0))"),
			"free-start IV differential must pair both CVs, got:\n{smt}"
		);
		assert!(
			smt.contains("; Assert starting vector different"),
			"missing CV-difference block, got:\n{smt}"
		);
		assert!(
			smt.contains(&format!("\t(distinct delta_a0 {zeros})\n")),
			"missing CV-difference assertion, got:\n{smt}"
		);
		assert!(
			!smt.contains("; Assert messages not the same"),
			"free-start must not assert message difference, got:\n{smt}"
		);
		assert!(
			smt.contains(&format!("\t(= delta_hash0 {zeros})\n")),
			"missing hash-equality assertion, got:\n{smt}"
		);
		assert!(
			section_positions(&smt).is_sorted(),
			"sections out of order, got:\n{smt}"
		);
	}

	#[test]
	fn dxor_and_dsub_differ_only_in_diff_operator() {
		for collision_type in [CollisionType::Standard, CollisionType::FreeStart] {
			for rounds in [1, 2] {
				let dxor = generated(collision_type, rounds);

				let mut dsub = dsub_builder(collision_type, rounds);
				DsubEncoding
					.generate(&mut dsub)
					.expect("dsub generation must succeed without a solver");

				assert_ne!(
					dxor, dsub.smt,
					"dxor and dsub outputs must differ in the diff operator"
				);

				let normalized_dxor = dxor.replace("(bvxor m0_", "(DIFF m0_");
				let normalized_dsub = dsub.smt.replace("(bvsub m0_", "(DIFF m0_");
				assert_eq!(
					normalized_dxor, normalized_dsub,
					"dxor and dsub must be identical modulo diff operator for \
					{collision_type:?} at {rounds} rounds"
				);
			}
		}
	}
}
