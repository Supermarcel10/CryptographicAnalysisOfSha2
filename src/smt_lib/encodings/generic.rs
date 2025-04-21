use crate::sha::StartVector;
use crate::smt_lib::smt_lib::SmtBuilder;
use crate::smt_lib::utilities::{get_previous_var, msg_prefix, smt_hex};
use crate::structs::collision_type::CollisionType;


impl SmtBuilder {
	pub(super)  fn title(&mut self, title: &str) {
		let break_like = if self.smt.len() != 0 {"\n\n"} else {""};
		self.smt += format!("{break_like};; {title}\n").as_str();
	}

	pub(super) fn comment(&mut self, comment: &str) {
		self.smt += format!("; {comment}\n").as_str();
	}

	pub(super) fn break_line(&mut self) {
		self.smt += "\n";
	}

	pub(super) fn set_logic(&mut self) {
		self.smt += "(set-option :produce-models true)\n(set-logic QF_BV)\n";
	}

	pub(super) fn define_word_type(&mut self) {
		let bit_size = self.hash_function.word_size().bits();
		self.smt += &format!("(define-sort Word () (_ BitVec {bit_size}))\n");
	}

	pub(super) fn define_functions(&mut self) {
		let word_size = self.hash_function.word_size().bits();

		let ch = "(define-fun ch ((e Word) (f Word) (g Word)) Word\n\t(bvxor (bvand e f) (bvand (bvnot e) g))\n)";
		let maj = "(define-fun maj ((a Word) (b Word) (c Word)) Word\n\t(bvxor (bvand a b) (bvand a c) (bvand b c))\n)";
		let sigma0 = "(define-fun sigma0 ((a Word)) Word\n\t(bvxor ((_ rotate_right 2) a) ((_ rotate_right 13) a) ((_ rotate_right 22) a))\n)";
		let sigma1 = "(define-fun sigma1 ((e Word)) Word\n\t(bvxor ((_ rotate_right 6) e) ((_ rotate_right 11) e) ((_ rotate_right 25) e))\n)";
		let gamma0 = format!("(define-fun gamma0 ((x Word)) Word\n\t(bvxor ((_ rotate_right 7) x) ((_ rotate_right 18) x) (bvlshr x (_ bv3 {word_size})))\n)");
		let gamma1 = format!("(define-fun gamma1 ((x Word)) Word\n\t(bvxor ((_ rotate_right 17) x) ((_ rotate_right 19) x) (bvlshr x (_ bv10 {word_size})))\n)");
		let t1 = "(define-fun t1 ((h Word) (e Word) (f Word) (g Word) (k Word) (w Word)) Word\n\t(bvadd h (sigma1 e) (ch e f g) k w)\n)";
		let t2 = "(define-fun t2 ((a Word) (b Word) (c Word)) Word\n\t(bvadd (sigma0 a) (maj a b c))\n)";
		let expand_message = "(define-fun expandMessage ((a Word) (b Word) (c Word) (d Word)) Word\n\t(bvadd a (gamma0 b) c (gamma1 d))\n)";

		self.smt += &format!("{ch}\n{maj}\n{sigma0}\n{sigma1}\n{gamma0}\n{gamma1}\n{t1}\n{t2}\n{expand_message}");
	}

	pub(super) fn define_constants(&mut self) {
		if self.rounds == 0 {
			self.comment("K constants irrelevant for 0 rounds");
			return;
		}

		self.comment("Define K constants");
		let k = self.hash_function.get_constant();

		// Only k[i] constants required, where i is number of compression rounds
		// Therefore, we only take the number of rounds required

		let mut s = String::new();
		for (i, val) in k.iter().take(self.rounds as usize).enumerate() {
			s += &format!("(define-fun k{i} () Word {})\n", smt_hex(*val, &self.hash_function))
		};

		self.smt += &s;
	}

	pub(super) fn define_expansion_for_message(&mut self, message: u8) {
		self.comment(&format!("MESSAGE {message}"));
		let msg = format!("m{message}_w");

		// Only w[i] required, where i is number of compression rounds
		// Therefore, we only take the number of rounds required, and initialize the first 16 as 0.

		self.comment("Initial state");
		let mut s = String::new();
		for i in 0..self.rounds.min(16) {
			if i < self.rounds.min(16) {
				s += &format!("(declare-fun {msg}{i} () Word)\n");
			} else {
				s += &format!(
					"(define-fun {msg}{i} () Word {}) ; Irrelevant for {} rounds\n",
					smt_hex(self.hash_function.default_word(), &self.hash_function),
					self.rounds,
				);
			}
		}
		self.smt += &s;

		if self.rounds <= 16 {
			self.comment(&format!("Message expansion irrelevant for {} rounds", self.rounds));
		} else {
			self.break_line();
			self.comment("Message expansion");
			for i in 16..self.rounds {
				self.smt += &format!(
					"(define-fun {msg}{i} () Word (expandMessage {msg}{} {msg}{} {msg}{} {msg}{}))\n",
					i - 16, i - 15, i - 7, i - 2
				)
			}
		}
	}

	pub(super) fn define_differential_expansion(&mut self) {
		self.define_expansion_for_message(0);
		self.break_line();
		self.comment("Message Differential (W)");
		for i in 0..self.rounds.min(16) {
			self.smt += &format!("(declare-fun delta_w{i} () Word)\n");
		}

		self.break_line();
		self.comment("MESSAGE 1 (Derived)");
		for i in 0..self.rounds.min(16) {
			self.smt += &format!("(define-fun m1_w{i} () Word (bvxor m0_w{i} delta_w{i}))\n");
		}

		if self.rounds <= 16 {
			self.comment(&format!("Message expansion assertions irrelevant for {} rounds", self.rounds));
		} else {
			self.break_line();
			self.comment("Message Expansion Assertions");
			// TODO: This can be updated to reason fully only about differnces, if the input later down the line can reason about only differences.
			for i in 16..self.rounds {
				self.smt += &format!(
					"(define-fun m1_w{i} () Word (expandMessage m1_w{} m1_w{} m1_w{} m1_w{}))\n",
					i - 16, i - 15, i - 7, i - 2
				);
			}
		}
	}

	pub(super) fn define_compression_for_message(&mut self, message: u8) {
		self.comment(&format!("MESSAGE {message}"));

		let mut s = String::new();
		for i in 1..=self.rounds {
			let prev = i - 1;
			let msg = &msg_prefix(message, prev.into(), self.collision_type);

			s.push_str(&format!("(define-fun m{message}_t1_{i} () Word (t1 {msg}h{prev} {msg}e{prev} {msg}f{prev} {msg}g{prev} k{prev} m{message}_w{prev}))\n\
				(define-fun m{message}_t2_{i} () Word (t2 {msg}a{prev} {msg}b{prev} {msg}c{prev}))\n"));

			for var in 'a'..='h' {
				if var == 'a' {
					s.push_str(&format!("(define-fun m{message}_{var}{i} () Word (bvadd m{message}_t1_{i} m{message}_t2_{i}))\n"))
				} else if var == 'e' {
					s.push_str(&format!("(define-fun m{message}_{var}{i} () Word (bvadd {msg}d{prev} m{message}_t1_{i}))\n"))
				} else {
					let prev_var = get_previous_var(var);
					s.push_str(&format!("(define-fun m{message}_{var}{i} () Word {msg}{prev_var}{prev})\n"))
				}
			}
		}

		self.smt += &s;
	}

	pub(super) fn define_differential_for_working_variables(&mut self) {
		self.comment("Variable Differential");

		for i in 1..=self.rounds {
			for var in 'a'..='h' {
				self.smt += &format!(
					"(define-fun delta_{var}{i} () Word (bvxor m0_{var}{i} m1_{var}{i}))\n"
				);
			}
		}
	}

	pub(super) fn define_initial_vector(&mut self) {
		self.comment("Define H constants (IV/CV)");
		use crate::structs::collision_type::CollisionType::*;

		let iv_vec = StartVector::IV.get_vector(self.hash_function);
		let mut s = String::new();
		for (i, var) in ('a'..='h').enumerate() {
			s += &match self.collision_type {
				Standard => format!("(define-fun {var}0 () Word {})\n", smt_hex(iv_vec[i], &self.hash_function)),
				SemiFreeStart => format!("(declare-fun {var}0 () Word)\n"),
				FreeStart => format!("(declare-fun m0_{var}0 () Word)\n(declare-fun m1_{var}0 () Word)\n"),
			}
		}

		self.smt += &s;
	}

	pub(super) fn final_state_update(&mut self) {
		self.comment("Final state update");

		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		for (i, var) in ('a'..='h').take(final_size).enumerate() {
			for m in 0..2 {
				let msg_round0 = msg_prefix(m, 0, self.collision_type);
				let msg = msg_prefix(m, self.rounds.into(), self.collision_type);
				self.smt += &format!("(define-fun m{m}_hash{i} () Word (bvadd {msg_round0}{var}0 {msg}{var}{round}))\n",
									 round = self.rounds);
			}
		}
	}

	pub(super) fn check_sat(&mut self) {
		self.title("GO!");
		self.smt += "(check-sat)\n";
	}

	pub(super) fn get_full_model(&mut self) {
		self.title("GET OUTPUT");

		self.comment("H Constants (IV/CV)");
		let mut h = String::new();
		for var in 'a'..='h' {
			if self.collision_type == CollisionType::FreeStart {
				h += &format!("m0_{var}0 m1_{var}0 ");
			} else {
				h += &format!("{var}0 ");
			}
		}
		self.smt += &format!("(get-value ({}))\n", h.trim());
		self.break_line();

		self.comment("Output hash");
		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		let mut hash = String::new();
		for i in 0..final_size {
			hash += &format!("m0_hash{i} ");
		}
		self.smt += &format!("(get-value ({}))\n", hash.trim());

		if self.rounds == 0 {
			return;
		}

		self.break_line();
		self.comment("Output round A/E/W state changes");
		let mut s = String::new();
		for i in 0..self.rounds {
			for var in ['a', 'e', 'w'] {
				if i == 0 && self.collision_type != CollisionType::FreeStart && var != 'w' {
					s += &format!("{var}{i} ");
				} else {
					for m in 0..2 {
						s += &format!("m{m}_{var}{i} ");
					}
				}
			}
		}
		self.smt += &format!("(get-value ({}))\n", s.trim());
	}
}
