use anyhow::Result;
use sha2_core::structs::collision_type::CollisionType;

use crate::smt_lib::builder::SmtBuilder;

impl SmtBuilder {
	fn assert_initial_vector_not_same(&mut self) {
		self.comment("Assert starting vectors (CV) not the same");

		let mut s = String::new();
		for var in 'a'..='h' {
			s += &format!("\t(distinct m0_{var}0 m1_{var}0)\n")
		}

		self.smt += &format!("(assert (or\n{s}))\n");
	}

	fn assert_messages_not_same(&mut self) {
		self.comment("Assert messages not the same");

		let mut s = String::new();
		for i in 0..self.rounds.min(16) {
			s += &format!("\t(distinct m0_w{i} m1_w{i})\n");
		}

		if self.rounds == 1 {
			self.smt += &format!("(assert\n{s})\n");
		} else if self.rounds > 1 {
			self.smt += &format!("(assert (or\n{s}))\n");
		}
	}

	fn assert_hash_same(&mut self) {
		self.comment("Assert output hash is the same");

		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		let mut s = String::new();
		for i in 0..final_size {
			s += &format!("\t(= m0_hash{i} m1_hash{i})\n");
		}

		self.smt += format!("(assert (and\n{s}))\n").as_str();
	}

	pub fn brute_force_encoding(&mut self) -> Result<()> {
		self.title("SETUP");
		self.set_logic();

		self.title("TYPE");
		self.define_word_type();

		self.title("FUNCTIONS");
		self.define_functions()?;

		self.title("CONSTANTS");
		self.define_constants();
		self.break_line();
		self.define_initial_vector();

		self.title("MESSAGE EXPANSION");
		self.define_expansion_for_message(0);
		self.break_line();
		self.define_expansion_for_message(1);

		self.title("MESSAGE COMPRESSION");
		self.define_compression_for_message(0)?;
		self.break_line();
		self.define_compression_for_message(1)?;
		self.break_line();
		self.final_state_update()?;

		self.title("ASSERTIONS");
		if self.collision_type == CollisionType::FreeStart {
			self.assert_initial_vector_not_same();
		} else {
			self.assert_messages_not_same();
		}
		self.break_line();

		self.assert_hash_same();

		self.check_sat();
		self.get_full_model();
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use sha2_core::structs::hash_function::HashFunction;

	use super::*;
	use crate::smt_lib::smt_retriever::EncodingType;

	fn brute_force_builder(collision_type : CollisionType, rounds : u8) -> SmtBuilder {
		SmtBuilder {
			smt : String::new(),
			hash_function : HashFunction::SHA256,
			rounds,
			collision_type,
			encoding : EncodingType::BruteForce {
				simplified_maj_and_ch_functions : false,
				alternative_add : false
			}
		}
	}

	fn generated(collision_type : CollisionType, rounds : u8) -> String {
		let mut builder = brute_force_builder(collision_type, rounds);
		builder
			.brute_force_encoding()
			.expect("brute-force generation must succeed without a solver");
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
	fn generation_declares_absolute_words_without_deltas() {
		for collision_type in [CollisionType::Standard, CollisionType::FreeStart] {
			let smt = generated(collision_type, 1);

			assert!(
				smt.contains("(declare-fun m0_w0 () Word)"),
				"missing absolute message word for {collision_type:?}, got:\n{smt}"
			);
			assert!(
				smt.contains("(declare-fun m1_w0 () Word)"),
				"missing second absolute message word for {collision_type:?}, got:\n{smt}"
			);
			assert!(
				!smt.contains("delta_"),
				"brute-force output must not define differentials for {collision_type:?}, got:\n{smt}"
			);
		}
	}

	#[test]
	fn standard_generation_asserts_messages_not_same_and_hash_same() {
		let one = generated(CollisionType::Standard, 1);
		assert!(
			one.contains("; Assert messages not the same"),
			"missing message-difference block, got:\n{one}"
		);
		assert!(
			one.contains("\t(distinct m0_w0 m1_w0)\n"),
			"missing absolute message-difference assertion, got:\n{one}"
		);
		assert!(
			one.contains("; Assert output hash is the same"),
			"missing hash-equality block, got:\n{one}"
		);
		assert!(
			one.contains("\t(= m0_hash0 m1_hash0)\n"),
			"missing absolute hash-equality assertion, got:\n{one}"
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
			two.contains("\t(distinct m0_w1 m1_w1)\n"),
			"missing second-round message-difference assertion, got:\n{two}"
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
	fn free_start_generation_asserts_cv_not_same_and_hash_same() {
		let smt = generated(CollisionType::FreeStart, 1);

		assert!(
			smt.contains("; Assert starting vectors (CV) not the same"),
			"missing CV-difference block, got:\n{smt}"
		);
		assert!(
			smt.contains("\t(distinct m0_a0 m1_a0)\n"),
			"missing absolute CV-difference assertion, got:\n{smt}"
		);
		assert!(
			!smt.contains("; Assert messages not the same"),
			"free-start must not assert message difference, got:\n{smt}"
		);
		assert!(
			smt.contains("\t(= m0_hash0 m1_hash0)\n"),
			"missing absolute hash-equality assertion, got:\n{smt}"
		);
		assert!(
			section_positions(&smt).is_sorted(),
			"sections out of order, got:\n{smt}"
		);
	}
}
