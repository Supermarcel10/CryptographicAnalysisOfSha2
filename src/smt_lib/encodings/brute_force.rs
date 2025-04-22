use crate::smt_lib::smt_lib::SmtBuilder;
use crate::structs::collision_type::CollisionType;


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

	pub fn brute_force_encoding(
		&mut self,
		simplified: bool,
	) {
		self.title("SETUP");
		self.set_logic();

		self.title("TYPE");
		self.define_word_type();

		self.title("FUNCTIONS");
		self.define_functions(simplified, simplified);

		self.title("CONSTANTS");
		self.define_constants();
		self.break_line();
		self.define_initial_vector();

		self.title("MESSAGE EXPANSION");
		self.define_expansion_for_message(0);
		self.break_line();
		self.define_expansion_for_message(1);

		self.title("MESSAGE COMPRESSION");
		self.define_compression_for_message(0);
		self.break_line();
		self.define_compression_for_message(1);
		self.break_line();
		self.final_state_update();

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
	}
}
