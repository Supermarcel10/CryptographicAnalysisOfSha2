use std::error::Error;
use crate::smt_lib::smt_lib::SmtBuilder;
use crate::structs::collision_type::CollisionType;


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
					"0".repeat(word_size));
			} else {
				self.smt += &format!("(declare-fun delta_{var}0 () Word)\n");
			}
		}
	}

	// fn define_base4_differential_compression(&mut self) {
	// 	for i in 1..=self.rounds {
	// 		let prev = i - 1;
	//
	// 		self.smt += &format!("(define-fun delta_t1_{i} () Word (t1 delta_h{prev} delta_e{prev} delta_f{prev} delta_g{prev} delta_k{prev} delta_w{prev}))\n\
	// 			(define-fun delta_t2_{i} () Word (t2 delta_a{prev} delta_b{prev} delta_c{prev}))\n");
	//
	// 		for var in 'a'..='h' {
	// 			if var == 'a' {
	// 				self.smt += &format!("(define-fun delta_{var}{i} () Word (bvadd delta_t1_{i} delta_t2_{i}))\n");
	// 			} else if var == 'e' {
	// 				self.smt += &format!("(define-fun delta_{var}{i} () Word (bvadd delta_d{prev} delta_t1_{i}))\n");
	// 			} else {
	// 				let prev_var = get_previous_var(var);
	// 				self.smt += &format!("(define-fun delta_{var}{i} () Word delta_{prev_var}{prev})\n");
	// 			}
	// 		}
	// 	}
	// }
	//
	// fn define_base4_differential_hash_state(&mut self) {
	// 	self.comment("Final state difference");
	//
	// 	let max_round = self.rounds;
	// 	let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
	// 	for (i, var) in ('a'..='h').take(final_size).enumerate() {
	// 		self.smt += &format!("(define-fun delta_hash{i} () Word (bvadd delta_{var}0 delta_{var}{max_round}))\n");
	// 	}
	// }
	//
	// fn get_base4_full_model_differential(&mut self) {
	// 	self.title("GET OUTPUT");
	//
	// 	self.comment("Input message");
	// 	let mut message = String::new();
	// 	for i in 0..=self.rounds.min(7) {
	// 		message += &format!("m0_w{i} m1_w{i} ");
	// 	}
	// 	self.smt += &format!("(get-value ({}))\n", message.trim());
	//
	// 	if self.rounds == 0 {
	// 		return;
	// 	}
	//
	// 	self.break_line();
	// 	self.comment("Output round A/E/W state changes");
	// 	let mut s = String::new();
	// 	for i in 0..self.rounds {
	// 		for var in ['a', 'e', 'w'] {
	// 			if i == 0 && self.collision_type != CollisionType::FreeStart && var != 'w' {
	// 				s += &format!("delta_{var}{i} ");
	// 			} else {
	// 				s += &format!("delta_{var}{i} ");
	// 			}
	// 		}
	// 	}
	// 	self.smt += &format!("(get-value ({}))\n", s.trim());
	// }

	pub fn base4_encoding(&mut self) -> Result<(), Box<dyn Error>> {
		// TODO: Implement
		self.title("SETUP");
		self.set_logic();

		self.title("TYPE");
		self.define_word_type();

		self.title("FUNCTIONS");
		self.define_functions();

		self.title("CONSTANTS");
		self.define_base4_differential_constants();
		self.break_line();
		self.define_base4_differential_initial_vector();

		self.title("MESSAGE EXPANSION");
		// self.define_differential_words();

		self.title("MESSAGE COMPRESSION");
		// self.define_base4_differential_compression();

		// self.break_line();
		// self.define_base4_differential_hash_state();

		self.title("ASSERTIONS");
		// if self.collision_type == CollisionType::FreeStart {
		// 	self.assert_initial_vector_different();
		// } else {
		// 	self.assert_message_difference();
		// }
		// self.break_line();

		// self.assert_hash_difference_equal();

		self.check_sat();
		self.get_full_model();

		Ok(())
	}
}
