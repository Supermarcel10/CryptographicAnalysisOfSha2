use std::error::Error;
use crate::smt_lib::smt_lib::SmtBuilder;
use crate::smt_lib::smt_retriever::EncodingType;
use crate::structs::collision_type::CollisionType;

impl SmtBuilder {
	pub(super) fn define_calculated_differential_initial_vector(
		&mut self,
		encoding_type: EncodingType,
	) -> Result<(), Box<dyn Error>> {
		let diff = encoding_type.get_diff()?;
		self.comment("Initial Vector difference");

		let word_size = self.hash_function.word_size().bits();
		for var in 'a'..='h' {
			if self.collision_type == CollisionType::FreeStart {
				self.smt += &format!("(define-fun delta_{var}0 () Word (bvxor m0_{var}0 m1_{var}0))\n");
			} else {
				self.smt += &format!("(define-fun delta_{var}0 () Word #b{})\n", "0".repeat(word_size));
			}
		}

		Ok(())
	}

	pub(super) fn define_differential_words(
		&mut self,
		encoding_type: EncodingType,
	) -> Result<(), Box<dyn Error>> {
		let diff = encoding_type.get_diff()?;

		self.define_expansion_for_message(0);
		self.break_line();
		self.define_expansion_for_message(1);
		self.break_line();

		self.comment("Message Differential (W)");
		for i in 0..self.rounds.min(16) {
			self.smt += &format!("(define-fun delta_w{i} () Word ({diff} m0_w{i} m1_w{i}))\n");
		}

		if self.rounds <= 16 {
			self.comment(&format!("Message expansion differentials irrelevant for {} rounds", self.rounds));
		} else {
			self.break_line();
			self.comment("Message Expansion Assertions");
			for i in 16..self.rounds {
				self.smt += &format!(
					"(define-fun delta_w{i} () Word (expandMessage delta_w{} delta_w{} delta_w{} delta_w{}))",
					i - 16, i - 15, i - 7, i - 2
				);
			}
		}

		Ok(())
	}

	pub(super) fn define_differential_for_working_variables(
		&mut self,
		encoding_type: EncodingType,
	) -> Result<(), Box<dyn Error>> {
		let diff = encoding_type.get_diff()?;
		self.comment("Variable Differential");

		for i in 1..=self.rounds {
			for var in 'a'..='h' {
				self.smt += &format!(
					"(define-fun delta_{var}{i} () Word ({diff} m0_{var}{i} m1_{var}{i}))\n"
				);
			}
		}

		Ok(())
	}

	pub(super) fn define_differential_final_state(
		&mut self,
		encoding_type: EncodingType,
	) -> Result<(), Box<dyn Error>> {
		let diff = encoding_type.get_diff()?;

		self.comment("Final state difference");

		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		for i in 0..final_size {
			self.smt += &format!("(define-fun delta_hash{i} () Word ({diff} m0_hash{i} m1_hash{i}))\n");
		}

		Ok(())
	}

	pub(super) fn assert_initial_vector_different(&mut self) {
		self.comment("Assert starting vector different");

		let word_size = self.hash_function.word_size().bits();
		let mut s = String::new();
		for var in 'a'..='h' {
			s += &format!("\t(distinct delta_{var}0 #b{})\n", "0".repeat(word_size));
		}

		self.smt += &format!("(assert (or\n{s}))\n");
	}

	pub(super) fn assert_message_difference(&mut self) {
		self.comment("Assert messages not the same");
		let word_size = self.hash_function.word_size().bits();

		let mut s = String::new();
		for i in 0..self.rounds.min(16) {
			s += &format!("\t(distinct delta_w{i} #b{})\n", "0".repeat(word_size));
		}

		if self.rounds == 1 {
			self.smt += &format!("(assert\n{s})\n");
		} else if self.rounds > 1 {
			self.smt += &format!("(assert (or\n{s}))\n");
		}
	}

	pub(super) fn assert_hash_difference_equal(&mut self) {
		self.comment("Assert difference in output hash is none");

		let word_size = self.hash_function.word_size().bits();
		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		let mut s = String::new();
		for i in 0..final_size {
			s += &format!("\t(= delta_hash{i} #b{})\n", "0".repeat(word_size));
		}

		self.smt += format!("(assert (and\n{s}))\n").as_str();
	}
}
