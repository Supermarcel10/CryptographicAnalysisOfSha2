use anyhow::Result;
use sha2_core::structs::collision_type::CollisionType;

use crate::smt_lib::builder::SmtBuilder;

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
