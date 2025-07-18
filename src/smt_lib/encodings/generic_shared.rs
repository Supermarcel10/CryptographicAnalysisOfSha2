use std::error::Error;
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

	pub(super) fn define_functions(&mut self) -> Result<(), Box<dyn Error>> {
		let word_size = self.hash_function.word_size().bits();
		let simplified = self.encoding.simplified_maj_and_ch_functions();

		// MAJ & CH simplification
		let ch = if simplified {
			"(define-fun ch ((e Word) (f Word) (g Word)) Word\n\t(bvor (bvand e f) (bvand (bvnot e) g))\n)"
		} else {
			"(define-fun ch ((e Word) (f Word) (g Word)) Word\n\t(bvxor (bvand e f) (bvand (bvnot e) g))\n)"
		};

		let maj = if simplified {
			"(define-fun maj ((a Word) (b Word) (c Word)) Word\n\t(bvor (bvand a b) (bvand a c) (bvand b c))\n)"
		} else {
			"(define-fun maj ((a Word) (b Word) (c Word)) Word\n\t(bvxor (bvand a b) (bvand a c) (bvand b c))\n)"
		};

		if self.encoding.alternative_add() {
			self.comment("Append bitwise adder and helpers if necessary");
			self.smt += &self.define_bitwise_add();
			self.break_line();
		}

		// ALT ADD
		let t1_add = self.add(vec!["h", "(sigma1 e)", "(ch e f g)", "k", "w"])?;
		let t2_add = self.add(vec!["(sigma0 a)", "(maj a b c)"])?;
		let expand_message_add = self.add(vec!["a", "(gamma0 b)", "c", "(gamma1 d)"])?;

		let sigma0 = "(define-fun sigma0 ((a Word)) Word\n\t(bvxor ((_ rotate_right 2) a) ((_ rotate_right 13) a) ((_ rotate_right 22) a))\n)";
		let sigma1 = "(define-fun sigma1 ((e Word)) Word\n\t(bvxor ((_ rotate_right 6) e) ((_ rotate_right 11) e) ((_ rotate_right 25) e))\n)";
		let gamma0 = format!("(define-fun gamma0 ((x Word)) Word\n\t(bvxor ((_ rotate_right 7) x) ((_ rotate_right 18) x) (bvlshr x (_ bv3 {word_size})))\n)");
		let gamma1 = format!("(define-fun gamma1 ((x Word)) Word\n\t(bvxor ((_ rotate_right 17) x) ((_ rotate_right 19) x) (bvlshr x (_ bv10 {word_size})))\n)");
		let t1 = format!("(define-fun t1 ((h Word) (e Word) (f Word) (g Word) (k Word) (w Word)) Word\n\t{t1_add}\n)");
		let t2 = format!("(define-fun t2 ((a Word) (b Word) (c Word)) Word\n\t{t2_add}\n)");
		let expand_message = format!("(define-fun expandMessage ((a Word) (b Word) (c Word) (d Word)) Word\n\t{expand_message_add}\n)");

		self.smt += &format!("{ch}\n{maj}\n{sigma0}\n{sigma1}\n{gamma0}\n{gamma1}\n{t1}\n{t2}\n{expand_message}");
		Ok(())
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

	pub(super) fn define_compression_for_message(&mut self, message: u8) -> Result<(), Box<dyn Error>> {
		self.comment(&format!("MESSAGE {message}"));

		let mut s = String::new();
		for i in 1..=self.rounds {
			let prev = i - 1;
			let msg = &msg_prefix(message, prev.into(), self.collision_type);

			s.push_str(&format!("(define-fun m{message}_t1_{i} () Word (t1 {msg}h{prev} {msg}e{prev} {msg}f{prev} {msg}g{prev} k{prev} m{message}_w{prev}))\n\
				(define-fun m{message}_t2_{i} () Word (t2 {msg}a{prev} {msg}b{prev} {msg}c{prev}))\n"));

			for var in 'a'..='h' {
				if var == 'a' {
					let a_add = self.add(vec![
						&format!("m{message}_t1_{i}"),
						&format!("m{message}_t2_{i}"),
					])?;

					s.push_str(&format!("(define-fun m{message}_{var}{i} () Word {a_add})\n"))
				} else if var == 'e' {
					let e_add = self.add(vec![
						&format!("{msg}d{prev}"),
						&format!("m{message}_t1_{i}"),
					])?;

					s.push_str(&format!("(define-fun m{message}_{var}{i} () Word {e_add})\n"))
				} else {
					let prev_var = get_previous_var(var);
					s.push_str(&format!("(define-fun m{message}_{var}{i} () Word {msg}{prev_var}{prev})\n"))
				}
			}
		}

		self.smt += &s;
		Ok(())
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

	pub(super) fn final_state_update(&mut self) -> Result<(), Box<dyn Error>> {
		self.comment("Final state update");

		let final_size = self.hash_function.truncate_to_length().unwrap_or(8);
		for (i, var) in ('a'..='h').take(final_size).enumerate() {
			for m in 0..2 {
				let msg_round0 = msg_prefix(m, 0, self.collision_type);
				let msg = msg_prefix(m, self.rounds.into(), self.collision_type);

				let state_update_add = self.add(vec![
					&format!("{msg_round0}{var}0"),
					&format!("{msg}{var}{round}", round = self.rounds)
				])?;

				self.smt += &format!("(define-fun m{m}_hash{i} () Word {state_update_add})\n");
			}
		}
		Ok(())
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
