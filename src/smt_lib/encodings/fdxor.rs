use crate::smt_lib::smt_lib::SmtBuilder;
use crate::smt_lib::utilities::get_previous_var;
use crate::structs::collision_type::CollisionType;


impl SmtBuilder {
	fn define_differential_constants(&mut self) {
		self.comment("Define K constant differential");

		let word_size = self.hash_function.word_size().bits();
		for i in 0..self.rounds {
			self.smt += &format!(
				"(define-fun delta_k{i} () Word #b{})\n",
				"0".repeat(word_size)
			);
		}
	}

	fn define_differential_initial_vector(&mut self) {
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

	fn define_differential_compression(&mut self) {
		for i in 1..=self.rounds {
			let prev = i - 1;

			self.smt += &format!("(define-fun delta_t1_{i} () Word (t1 delta_h{prev} delta_e{prev} delta_f{prev} delta_g{prev} delta_k{prev} delta_w{prev}))\n\
				(define-fun delta_t2_{i} () Word (t2 delta_a{prev} delta_b{prev} delta_c{prev}))\n");

			for var in 'a'..='h' {
				if var == 'a' {
					self.smt += &format!("(define-fun delta_{var}{i} () Word (bvadd delta_t1_{i} delta_t2_{i}))\n");
				} else if var == 'e' {
					self.smt += &format!("(define-fun delta_{var}{i} () Word (bvadd delta_d{prev} delta_t1_{i}))\n");
				} else {
					let prev_var = get_previous_var(var);
					self.smt += &format!("(define-fun delta_{var}{i} () Word delta_{prev_var}{prev})\n");
				}
			}
		}
	}

	fn define_differential_hash_state(&mut self) {
		self.comment("Final state difference");

		let max_round = self.rounds;
		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		for (i, var) in ('a'..='h').take(final_size).enumerate() {
			self.smt += &format!("(define-fun delta_hash{i} () Word (bvadd delta_{var}0 delta_{var}{max_round}))\n");
		}
	}

	fn get_full_model_differential(&mut self) {
		self.title("GET OUTPUT");

		self.comment("Input message");
		let mut message = String::new();
		for i in 0..=self.rounds.min(7) {
			message += &format!("m0_w{i} m1_w{i} ");
		}
		self.smt += &format!("(get-value ({}))\n", message.trim());

		if self.rounds == 0 {
			return;
		}

		self.break_line();
		self.comment("Output round A/E/W state changes");
		let mut s = String::new();
		for i in 0..self.rounds {
			for var in ['a', 'e', 'w'] {
				if i == 0 && self.collision_type != CollisionType::FreeStart && var != 'w' {
					s += &format!("delta_{var}{i} ");
				} else {
					s += &format!("delta_{var}{i} ");
				}
			}
		}
		self.smt += &format!("(get-value ({}))\n", s.trim());
	}

	pub fn full_dxor_encoding(&mut self) {
		self.title("SETUP");
		self.set_logic();

		self.title("TYPE");
		self.define_word_type();

		self.title("FUNCTIONS");
		self.define_functions();

		self.title("CONSTANTS");
		self.define_differential_constants();
		self.break_line();
		self.define_differential_initial_vector();

		self.title("MESSAGE EXPANSION");
		self.define_differential_expansion();

		self.title("MESSAGE COMPRESSION");
		self.define_differential_compression();

		self.break_line();
		self.define_differential_hash_state();

		self.title("ASSERTIONS");
		if self.collision_type == CollisionType::FreeStart {
			self.assert_initial_vector_different();
		} else {
			self.assert_message_difference();
		}
		self.break_line();

		self.assert_hash_difference_equal();

		self.check_sat();
		self.get_full_model_differential();
	}
}

// // AND
// (define-fun d2 () BV4 (bvand X_d Y_d))
// (define-fun b2 () BV4 (bvand (bvand X_f Y_f) (bvnot d2)))
// (define-fun c2 () BV4 (bvand (bvand X_g Y_g) (bvnot d2)))
// (define-fun a2 () BV4 (bvnot (bvor d2 (bvor c2 b2))))

// // OR
// (define-fun a2 () BV4 (bvand X_a Y_a))
// (define-fun b2 () BV4 (bvnot (bvor X_g Y_g a2)))
// (define-fun c2 () BV4 (bvnot (bvor X_f Y_f a2)))
// (define-fun d2 () BV4 (bvnot (bvor a2 b2 c2)))

// // XOR
// (define-fun a2 () BV4
// (bvor (bvand X_a Y_a)
// (bvand X_b Y_b)
// (bvand X_c Y_c)
// (bvand X_d Y_d)
// )
// )
//
// (define-fun b2 () BV4
// (bvor (bvand X_a Y_b)
// (bvand X_b Y_a)
// (bvand X_c Y_d)
// (bvand X_d Y_c)
// )
// )
//
// (define-fun c2 () BV4
// (bvor (bvand X_a Y_c)
// (bvand X_c Y_a)
// (bvand X_b Y_d)
// (bvand X_d Y_b)
// )
// )
//
// (define-fun d2 () BV4
// (bvor (bvand X_a Y_d)
// (bvand X_d Y_a)
// (bvand X_b Y_c)
// (bvand X_c Y_b)
// )
// )
