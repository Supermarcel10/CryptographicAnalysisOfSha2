use crate::smt_lib::smt_lib::SmtBuilder;
use crate::structs::collision_type::CollisionType;


impl SmtBuilder {
	fn define_differential_initial_vector(&mut self) {
		if self.collision_type != CollisionType::FreeStart {
			return;
		}

		self.comment("Initial Vector difference");

		for var in 'a'..='h' {
			self.smt += &format!("(define-fun delta_{var}0 () Word (bvxor m0_{var}0 m1_{var}0))");
		}
	}

	fn define_final_state_difference(&mut self) {
		self.comment("Final state difference");

		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		for i in 0..final_size {
			self.smt += &format!("(define-fun delta_hash{i} () Word (bvxor m0_hash{i} m1_hash{i}))\n");
		}
	}

	fn assert_initial_vector_different(&mut self) {
		self.comment("Assert starting vector different");

		let word_size = self.hash_function.word_size().bits();
		let mut s = String::new();
		for var in 'a'..='h' {
			s += &format!("(distinct delta_{var}0 #b{})", "0".repeat(word_size));
		}

		self.smt += &format!("(assert (or\n{s}))\n");
	}

	fn assert_message_difference(&mut self) {
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

	fn assert_hash_difference_equal(&mut self) {
		self.comment("Assert difference in output hash is none");

		let word_size = self.hash_function.word_size().bits();
		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		let mut s = String::new();
		for i in 0..final_size {
			s += &format!("\t(= delta_hash{i} #b{})\n", "0".repeat(word_size));
		}

		self.smt += format!("(assert (and\n{s}))\n").as_str();
	}

	pub fn dxor_encoding(&mut self) {
		self.title("SETUP");
		self.set_logic();

		self.title("TYPE");
		self.define_word_type();

		self.title("FUNCTIONS");
		self.define_functions();

		self.title("CONSTANTS");
		self.define_constants();
		self.break_line();
		self.define_initial_vector();
		self.break_line();
		self.define_differential_initial_vector();

		self.title("MESSAGE EXPANSION");
		self.define_differential_expansion();

		self.title("MESSAGE COMPRESSION");
		self.define_compression_for_message(0);
		self.break_line();
		self.define_compression_for_message(1);
		self.break_line();
		self.define_differential_for_working_variables();

		self.break_line();
		self.final_state_update();
		self.break_line();
		self.define_final_state_difference();

		self.title("ASSERTIONS");
		if self.collision_type == CollisionType::FreeStart {
			self.assert_initial_vector_different();
		} else {
			self.assert_message_difference();
		}
		self.break_line();

		self.assert_hash_difference_equal();

		self.check_sat();
		self.get_full_model();
	}
}
