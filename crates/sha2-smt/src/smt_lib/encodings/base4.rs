use anyhow::Result;
use sha2_core::structs::collision_type::CollisionType;

use crate::smt_lib::builder::SmtBuilder;
use crate::smt_lib::utilities::msg_prefix;

#[allow(unreachable_code)]
#[allow(dead_code)]
impl SmtBuilder {
	fn define_base4_differential_constants(&mut self) {
		self.comment("Define K constant differential");

		let word_size = self.hash_function.word_size().bits();
		for i in 0..self.rounds {
			self.smt += &format!(
				"(define-fun delta_k{i}_A () Word #b{})\n",
				"0".repeat(word_size)
			);
			self.smt += &format!(
				"(define-fun delta_k{i}_B () Word #b{})\n",
				"0".repeat(word_size)
			);
			self.smt += &format!(
				"(define-fun delta_k{i}_C () Word #b{})\n",
				"0".repeat(word_size)
			);
			self.smt += &format!(
				"(define-fun delta_k{i}_D () Word #b{})\n",
				"0".repeat(word_size)
			);
			self.smt += &format!(
				"(define-fun delta_k{i}_E () Word #b{})\n",
				"0".repeat(word_size)
			);
			self.smt += &format!(
				"(define-fun delta_k{i}_F () Word #b{})\n",
				"0".repeat(word_size)
			);
			self.smt += &format!(
				"(define-fun delta_k{i}_G () Word #b{})\n",
				"0".repeat(word_size)
			);
		}
	}

	fn define_base4_differential_initial_vector(&mut self) {
		self.comment("Define H constant differential (IV/CV)");

		let word_size = self.hash_function.word_size().bits();
		for var in 'a'..='h' {
			if self.collision_type == CollisionType::Standard {
				self.smt += &format!(
					"(define-fun delta_{var}0 () Word #b{})\n",
					"0".repeat(word_size)
				);
			} else {
				self.smt += &format!("(declare-fun delta_{var}0 () Word)\n");
			}
		}
	}

	fn b4_ones(&self) -> String {
		format!("#b{}", "1".repeat(self.hash_function.word_size().bits()))
	}

	/// Absolute SMT expression of working variable `var` of `message` at `round`.
	fn b4_abs(&self, message : u8, var : char, round : u64) -> String {
		format!(
			"{}{var}{round}",
			msg_prefix(message, round, self.collision_type)
		)
	}

	fn define_base4_pair(&mut self, tag : &str, left : &str, right : &str) {
		self.smt += &format!(
			"(define-fun B4_{tag}_A () Word (bvand (bvnot {left}) (bvnot {right})))\n\
			(define-fun B4_{tag}_B () Word (bvand (bvnot {left}) {right}))\n\
			(define-fun B4_{tag}_C () Word (bvand {left} (bvnot {right})))\n\
			(define-fun B4_{tag}_D () Word (bvand {left} {right}))\n"
		);
	}

	fn define_base4_conditions(&mut self) {
		self.comment("Base-4 condition masks for the chaining value");
		for var in 'a'..='h' {
			let (left, right) = match self.collision_type {
				CollisionType::FreeStart => (format!("m0_{var}0"), format!("m1_{var}0")),
				_ => {
					let shared = format!("{var}0");
					(shared.clone(), shared)
				}
			};
			self.define_base4_pair(&format!("cv_{var}"), &left, &right);
		}

		self.break_line();
		self.comment("Base-4 condition masks for the message schedule");
		for i in 0..self.rounds {
			self.define_base4_pair(&format!("w{i}"), &format!("m0_w{i}"), &format!("m1_w{i}"));
		}

		if self.rounds > 0 {
			self.break_line();
			self.comment("Base-4 condition masks for the working variables");
			for i in 1..=self.rounds {
				for var in 'a'..='h' {
					let left = self.b4_abs(0, var, i.into());
					let right = self.b4_abs(1, var, i.into());
					self.define_base4_pair(&format!("s{var}{i}"), &left, &right);
				}
			}
		}

		self.break_line();
		self.comment("Base-4 condition masks for the final hash");
		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		for i in 0..final_size {
			self.define_base4_pair(
				&format!("hash{i}"),
				&format!("m0_hash{i}"),
				&format!("m1_hash{i}")
			);
		}
	}

	pub fn base4_encoding(&mut self) -> Result<()> {
		todo!(); //TODO: Implement
		self.title("SETUP");
		self.set_logic();

		self.title("TYPE");
		self.define_word_type();

		self.title("FUNCTIONS");
		self.define_functions()?;

		self.title("CONSTANTS");
		self.define_base4_differential_constants();
		self.break_line();
		self.define_base4_differential_initial_vector();

		self.title("MESSAGE EXPANSION");

		self.title("MESSAGE COMPRESSION");

		self.title("ASSERTIONS");

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

	fn base4_builder(collision_type : CollisionType, rounds : u8) -> SmtBuilder {
		SmtBuilder {
			smt : String::new(),
			hash_function : HashFunction::SHA256,
			rounds,
			collision_type,
			encoding : EncodingType::Base4 {
				simplified_maj_and_ch_functions : false,
				alternative_add : false
			}
		}
	}

	#[test]
	fn ones_mask_matches_word_size() {
		let builder = base4_builder(CollisionType::Standard, 1);

		assert_eq!(builder.b4_ones(), format!("#b{}", "1".repeat(32)));
	}

	#[test]
	fn absolute_naming_uses_message_prefix() {
		let standard = base4_builder(CollisionType::Standard, 1);
		assert_eq!(standard.b4_abs(0, 'a', 0), "a0");
		assert_eq!(standard.b4_abs(1, 'a', 0), "a0");
		assert_eq!(standard.b4_abs(0, 'e', 3), "m0_e3");
		assert_eq!(standard.b4_abs(1, 'h', 3), "m1_h3");

		let free_start = base4_builder(CollisionType::FreeStart, 1);
		assert_eq!(free_start.b4_abs(0, 'a', 0), "m0_a0");
		assert_eq!(free_start.b4_abs(1, 'h', 0), "m1_h0");
	}

	#[test]
	fn pair_definition_shape() {
		let mut builder = base4_builder(CollisionType::Standard, 1);
		builder.define_base4_pair("w0", "m0_w0", "m1_w0");

		assert_eq!(
			builder.smt,
			"(define-fun B4_w0_A () Word (bvand (bvnot m0_w0) (bvnot m1_w0)))\n\
			(define-fun B4_w0_B () Word (bvand (bvnot m0_w0) m1_w0))\n\
			(define-fun B4_w0_C () Word (bvand m0_w0 (bvnot m1_w0)))\n\
			(define-fun B4_w0_D () Word (bvand m0_w0 m1_w0))\n"
		);
	}

	#[test]
	fn conditions_cover_cv_message_working_vars_and_hash() {
		let mut builder = base4_builder(CollisionType::Standard, 1);
		builder.define_base4_conditions();

		assert!(
			builder
				.smt
				.contains("; Base-4 condition masks for the chaining value"),
			"missing chaining-value section, got:\n{}",
			builder.smt
		);
		assert!(
			builder
				.smt
				.contains("(define-fun B4_cv_a_A () Word (bvand (bvnot a0) (bvnot a0)))"),
			"missing shared chaining-value pair, got:\n{}",
			builder.smt
		);
		assert!(
			builder
				.smt
				.contains("(define-fun B4_w0_D () Word (bvand m0_w0 m1_w0))"),
			"missing message pair, got:\n{}",
			builder.smt
		);
		assert!(
			builder
				.smt
				.contains("(define-fun B4_sa1_A () Word (bvand (bvnot m0_a1) (bvnot m1_a1)))"),
			"missing working-variable pair, got:\n{}",
			builder.smt
		);
		assert!(
			builder.smt.contains(
				"(define-fun B4_hash0_A () Word (bvand (bvnot m0_hash0) (bvnot m1_hash0)))"
			),
			"missing final-hash pair, got:\n{}",
			builder.smt
		);
	}

	#[test]
	fn conditions_use_separate_cvs_for_free_start() {
		let mut builder = base4_builder(CollisionType::FreeStart, 1);
		builder.define_base4_conditions();

		assert!(
			builder
				.smt
				.contains("(define-fun B4_cv_a_A () Word (bvand (bvnot m0_a0) (bvnot m1_a0)))"),
			"free-start chaining value must pair both CVs, got:\n{}",
			builder.smt
		);
	}

	#[test]
	fn conditions_skip_working_variables_for_zero_rounds() {
		let mut builder = base4_builder(CollisionType::Standard, 0);
		builder.define_base4_conditions();

		assert!(
			!builder.smt.contains("working variables"),
			"zero rounds must not emit working-variable masks, got:\n{}",
			builder.smt
		);
		assert!(
			builder
				.smt
				.contains("(define-fun B4_cv_h_D () Word (bvand h0 h0))"),
			"chaining-value masks must still be emitted, got:\n{}",
			builder.smt
		);
	}
}
