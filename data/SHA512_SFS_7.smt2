;; SETUP
(set-option :produce-models true)
(set-logic QF_BV)


;; TYPE
(define-sort Word () (_ BitVec 64))


;; FUNCTIONS
(define-fun ch ((e Word) (f Word) (g Word)) Word
	(bvxor (bvand e f) (bvand (bvnot e) g))
)
(define-fun maj ((a Word) (b Word) (c Word)) Word
	(bvxor (bvand a b) (bvand a c) (bvand b c))
)
(define-fun sigma0 ((a Word)) Word
	(bvxor ((_ rotate_right 2) a) ((_ rotate_right 13) a) ((_ rotate_right 22) a))
)
(define-fun sigma1 ((e Word)) Word
	(bvxor ((_ rotate_right 6) e) ((_ rotate_right 11) e) ((_ rotate_right 25) e))
)
(define-fun gamma0 ((x Word)) Word
	(bvxor ((_ rotate_right 7) x) ((_ rotate_right 18) x) (bvlshr x (_ bv3 32)))
)
(define-fun gamma1 ((x Word)) Word
	(bvxor ((_ rotate_right 17) x) ((_ rotate_right 19) x) (bvlshr x (_ bv10 32)))
)
(define-fun t1 ((h Word) (e Word) (f Word) (g Word) (k Word) (w Word)) Word
	(bvadd h (sigma1 e) (ch e f g) k w)
)
(define-fun t2 ((a Word) (b Word) (c Word)) Word
	(bvadd (sigma0 a) (maj a b c))
)
(define-fun expandMessage ((a Word) (b Word) (c Word) (d Word)) Word
	(bvadd a (gamma0 b) c (gamma1 d))
)

;; CONSTANTS
; Define K constants
(define-fun k0 () Word #x428a2f98d728ae22)
(define-fun k1 () Word #x7137449123ef65cd)
(define-fun k2 () Word #xb5c0fbcfec4d3b2f)
(define-fun k3 () Word #xe9b5dba58189dbbc)
(define-fun k4 () Word #x3956c25bf348b538)
(define-fun k5 () Word #x59f111f1b605d019)
(define-fun k6 () Word #x923f82a4af194f9b)

; Define H constants (IV/CV)
(declare-fun a0 () Word)
(declare-fun b0 () Word)
(declare-fun c0 () Word)
(declare-fun d0 () Word)
(declare-fun e0 () Word)
(declare-fun f0 () Word)
(declare-fun g0 () Word)
(declare-fun h0 () Word)


;; MESSAGE EXPANSION
; MESSAGE 0
; Initial state
(declare-fun m0_w0 () Word)
(declare-fun m0_w1 () Word)
(declare-fun m0_w2 () Word)
(declare-fun m0_w3 () Word)
(declare-fun m0_w4 () Word)
(declare-fun m0_w5 () Word)
(declare-fun m0_w6 () Word)
(define-fun m0_w7 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m0_w8 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m0_w9 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m0_w10 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m0_w11 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m0_w12 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m0_w13 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m0_w14 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m0_w15 () Word #x0000000000000000) ; Irrelevant for 7 rounds
; Message expansion irrelevant for 7 rounds

; MESSAGE 1
; Initial state
(declare-fun m1_w0 () Word)
(declare-fun m1_w1 () Word)
(declare-fun m1_w2 () Word)
(declare-fun m1_w3 () Word)
(declare-fun m1_w4 () Word)
(declare-fun m1_w5 () Word)
(declare-fun m1_w6 () Word)
(define-fun m1_w7 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m1_w8 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m1_w9 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m1_w10 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m1_w11 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m1_w12 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m1_w13 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m1_w14 () Word #x0000000000000000) ; Irrelevant for 7 rounds
(define-fun m1_w15 () Word #x0000000000000000) ; Irrelevant for 7 rounds
; Message expansion irrelevant for 7 rounds


;; MESSAGE COMPRESSION
; MESSAGE 0
(define-fun m0_t1_1 () Word (t1 h0 e0 f0 g0 k0 m0_w0))
(define-fun m0_t2_1 () Word (t2 a0 b0 c0))
(define-fun m0_a1 () Word (bvadd m0_t1_1 m0_t2_1))
(define-fun m0_b1 () Word a0)
(define-fun m0_c1 () Word b0)
(define-fun m0_d1 () Word c0)
(define-fun m0_e1 () Word (bvadd d0 m0_t1_1))
(define-fun m0_f1 () Word e0)
(define-fun m0_g1 () Word f0)
(define-fun m0_h1 () Word g0)
(define-fun m0_t1_2 () Word (t1 m0_h1 m0_e1 m0_f1 m0_g1 k1 m0_w1))
(define-fun m0_t2_2 () Word (t2 m0_a1 m0_b1 m0_c1))
(define-fun m0_a2 () Word (bvadd m0_t1_2 m0_t2_2))
(define-fun m0_b2 () Word m0_a1)
(define-fun m0_c2 () Word m0_b1)
(define-fun m0_d2 () Word m0_c1)
(define-fun m0_e2 () Word (bvadd m0_d1 m0_t1_2))
(define-fun m0_f2 () Word m0_e1)
(define-fun m0_g2 () Word m0_f1)
(define-fun m0_h2 () Word m0_g1)
(define-fun m0_t1_3 () Word (t1 m0_h2 m0_e2 m0_f2 m0_g2 k2 m0_w2))
(define-fun m0_t2_3 () Word (t2 m0_a2 m0_b2 m0_c2))
(define-fun m0_a3 () Word (bvadd m0_t1_3 m0_t2_3))
(define-fun m0_b3 () Word m0_a2)
(define-fun m0_c3 () Word m0_b2)
(define-fun m0_d3 () Word m0_c2)
(define-fun m0_e3 () Word (bvadd m0_d2 m0_t1_3))
(define-fun m0_f3 () Word m0_e2)
(define-fun m0_g3 () Word m0_f2)
(define-fun m0_h3 () Word m0_g2)
(define-fun m0_t1_4 () Word (t1 m0_h3 m0_e3 m0_f3 m0_g3 k3 m0_w3))
(define-fun m0_t2_4 () Word (t2 m0_a3 m0_b3 m0_c3))
(define-fun m0_a4 () Word (bvadd m0_t1_4 m0_t2_4))
(define-fun m0_b4 () Word m0_a3)
(define-fun m0_c4 () Word m0_b3)
(define-fun m0_d4 () Word m0_c3)
(define-fun m0_e4 () Word (bvadd m0_d3 m0_t1_4))
(define-fun m0_f4 () Word m0_e3)
(define-fun m0_g4 () Word m0_f3)
(define-fun m0_h4 () Word m0_g3)
(define-fun m0_t1_5 () Word (t1 m0_h4 m0_e4 m0_f4 m0_g4 k4 m0_w4))
(define-fun m0_t2_5 () Word (t2 m0_a4 m0_b4 m0_c4))
(define-fun m0_a5 () Word (bvadd m0_t1_5 m0_t2_5))
(define-fun m0_b5 () Word m0_a4)
(define-fun m0_c5 () Word m0_b4)
(define-fun m0_d5 () Word m0_c4)
(define-fun m0_e5 () Word (bvadd m0_d4 m0_t1_5))
(define-fun m0_f5 () Word m0_e4)
(define-fun m0_g5 () Word m0_f4)
(define-fun m0_h5 () Word m0_g4)
(define-fun m0_t1_6 () Word (t1 m0_h5 m0_e5 m0_f5 m0_g5 k5 m0_w5))
(define-fun m0_t2_6 () Word (t2 m0_a5 m0_b5 m0_c5))
(define-fun m0_a6 () Word (bvadd m0_t1_6 m0_t2_6))
(define-fun m0_b6 () Word m0_a5)
(define-fun m0_c6 () Word m0_b5)
(define-fun m0_d6 () Word m0_c5)
(define-fun m0_e6 () Word (bvadd m0_d5 m0_t1_6))
(define-fun m0_f6 () Word m0_e5)
(define-fun m0_g6 () Word m0_f5)
(define-fun m0_h6 () Word m0_g5)
(define-fun m0_t1_7 () Word (t1 m0_h6 m0_e6 m0_f6 m0_g6 k6 m0_w6))
(define-fun m0_t2_7 () Word (t2 m0_a6 m0_b6 m0_c6))
(define-fun m0_a7 () Word (bvadd m0_t1_7 m0_t2_7))
(define-fun m0_b7 () Word m0_a6)
(define-fun m0_c7 () Word m0_b6)
(define-fun m0_d7 () Word m0_c6)
(define-fun m0_e7 () Word (bvadd m0_d6 m0_t1_7))
(define-fun m0_f7 () Word m0_e6)
(define-fun m0_g7 () Word m0_f6)
(define-fun m0_h7 () Word m0_g6)

; MESSAGE 1
(define-fun m1_t1_1 () Word (t1 h0 e0 f0 g0 k0 m1_w0))
(define-fun m1_t2_1 () Word (t2 a0 b0 c0))
(define-fun m1_a1 () Word (bvadd m1_t1_1 m1_t2_1))
(define-fun m1_b1 () Word a0)
(define-fun m1_c1 () Word b0)
(define-fun m1_d1 () Word c0)
(define-fun m1_e1 () Word (bvadd d0 m1_t1_1))
(define-fun m1_f1 () Word e0)
(define-fun m1_g1 () Word f0)
(define-fun m1_h1 () Word g0)
(define-fun m1_t1_2 () Word (t1 m1_h1 m1_e1 m1_f1 m1_g1 k1 m1_w1))
(define-fun m1_t2_2 () Word (t2 m1_a1 m1_b1 m1_c1))
(define-fun m1_a2 () Word (bvadd m1_t1_2 m1_t2_2))
(define-fun m1_b2 () Word m1_a1)
(define-fun m1_c2 () Word m1_b1)
(define-fun m1_d2 () Word m1_c1)
(define-fun m1_e2 () Word (bvadd m1_d1 m1_t1_2))
(define-fun m1_f2 () Word m1_e1)
(define-fun m1_g2 () Word m1_f1)
(define-fun m1_h2 () Word m1_g1)
(define-fun m1_t1_3 () Word (t1 m1_h2 m1_e2 m1_f2 m1_g2 k2 m1_w2))
(define-fun m1_t2_3 () Word (t2 m1_a2 m1_b2 m1_c2))
(define-fun m1_a3 () Word (bvadd m1_t1_3 m1_t2_3))
(define-fun m1_b3 () Word m1_a2)
(define-fun m1_c3 () Word m1_b2)
(define-fun m1_d3 () Word m1_c2)
(define-fun m1_e3 () Word (bvadd m1_d2 m1_t1_3))
(define-fun m1_f3 () Word m1_e2)
(define-fun m1_g3 () Word m1_f2)
(define-fun m1_h3 () Word m1_g2)
(define-fun m1_t1_4 () Word (t1 m1_h3 m1_e3 m1_f3 m1_g3 k3 m1_w3))
(define-fun m1_t2_4 () Word (t2 m1_a3 m1_b3 m1_c3))
(define-fun m1_a4 () Word (bvadd m1_t1_4 m1_t2_4))
(define-fun m1_b4 () Word m1_a3)
(define-fun m1_c4 () Word m1_b3)
(define-fun m1_d4 () Word m1_c3)
(define-fun m1_e4 () Word (bvadd m1_d3 m1_t1_4))
(define-fun m1_f4 () Word m1_e3)
(define-fun m1_g4 () Word m1_f3)
(define-fun m1_h4 () Word m1_g3)
(define-fun m1_t1_5 () Word (t1 m1_h4 m1_e4 m1_f4 m1_g4 k4 m1_w4))
(define-fun m1_t2_5 () Word (t2 m1_a4 m1_b4 m1_c4))
(define-fun m1_a5 () Word (bvadd m1_t1_5 m1_t2_5))
(define-fun m1_b5 () Word m1_a4)
(define-fun m1_c5 () Word m1_b4)
(define-fun m1_d5 () Word m1_c4)
(define-fun m1_e5 () Word (bvadd m1_d4 m1_t1_5))
(define-fun m1_f5 () Word m1_e4)
(define-fun m1_g5 () Word m1_f4)
(define-fun m1_h5 () Word m1_g4)
(define-fun m1_t1_6 () Word (t1 m1_h5 m1_e5 m1_f5 m1_g5 k5 m1_w5))
(define-fun m1_t2_6 () Word (t2 m1_a5 m1_b5 m1_c5))
(define-fun m1_a6 () Word (bvadd m1_t1_6 m1_t2_6))
(define-fun m1_b6 () Word m1_a5)
(define-fun m1_c6 () Word m1_b5)
(define-fun m1_d6 () Word m1_c5)
(define-fun m1_e6 () Word (bvadd m1_d5 m1_t1_6))
(define-fun m1_f6 () Word m1_e5)
(define-fun m1_g6 () Word m1_f5)
(define-fun m1_h6 () Word m1_g5)
(define-fun m1_t1_7 () Word (t1 m1_h6 m1_e6 m1_f6 m1_g6 k6 m1_w6))
(define-fun m1_t2_7 () Word (t2 m1_a6 m1_b6 m1_c6))
(define-fun m1_a7 () Word (bvadd m1_t1_7 m1_t2_7))
(define-fun m1_b7 () Word m1_a6)
(define-fun m1_c7 () Word m1_b6)
(define-fun m1_d7 () Word m1_c6)
(define-fun m1_e7 () Word (bvadd m1_d6 m1_t1_7))
(define-fun m1_f7 () Word m1_e6)
(define-fun m1_g7 () Word m1_f6)
(define-fun m1_h7 () Word m1_g6)

; Final state update
(define-fun m0_hash0 () Word (bvadd a0 m0_a7))
(define-fun m1_hash0 () Word (bvadd a0 m1_a7))
(define-fun m0_hash1 () Word (bvadd b0 m0_b7))
(define-fun m1_hash1 () Word (bvadd b0 m1_b7))
(define-fun m0_hash2 () Word (bvadd c0 m0_c7))
(define-fun m1_hash2 () Word (bvadd c0 m1_c7))
(define-fun m0_hash3 () Word (bvadd d0 m0_d7))
(define-fun m1_hash3 () Word (bvadd d0 m1_d7))
(define-fun m0_hash4 () Word (bvadd e0 m0_e7))
(define-fun m1_hash4 () Word (bvadd e0 m1_e7))
(define-fun m0_hash5 () Word (bvadd f0 m0_f7))
(define-fun m1_hash5 () Word (bvadd f0 m1_f7))
(define-fun m0_hash6 () Word (bvadd g0 m0_g7))
(define-fun m1_hash6 () Word (bvadd g0 m1_g7))
(define-fun m0_hash7 () Word (bvadd h0 m0_h7))
(define-fun m1_hash7 () Word (bvadd h0 m1_h7))


;; ASSERTIONS
; Assert messages not the same
(assert (or
	(distinct m0_w0 m1_w0)
	(distinct m0_w1 m1_w1)
	(distinct m0_w2 m1_w2)
	(distinct m0_w3 m1_w3)
	(distinct m0_w4 m1_w4)
	(distinct m0_w5 m1_w5)
	(distinct m0_w6 m1_w6)
	(distinct m0_w7 m1_w7)
	(distinct m0_w8 m1_w8)
	(distinct m0_w9 m1_w9)
	(distinct m0_w10 m1_w10)
	(distinct m0_w11 m1_w11)
	(distinct m0_w12 m1_w12)
	(distinct m0_w13 m1_w13)
	(distinct m0_w14 m1_w14)
	(distinct m0_w15 m1_w15)
))

; Assert output hash is the same
(assert (and
	(= m0_hash0 m1_hash0)
	(= m0_hash1 m1_hash1)
	(= m0_hash2 m1_hash2)
	(= m0_hash3 m1_hash3)
	(= m0_hash4 m1_hash4)
	(= m0_hash5 m1_hash5)
	(= m0_hash6 m1_hash6)
	(= m0_hash7 m1_hash7)
))


;; GO!
(check-sat)


;; GET OUTPUT
; H Constants (IV/CV)
(get-value (a0 b0 c0 d0 e0 f0 g0 h0))

; Output hash
(get-value (m0_hash0 m0_hash1 m0_hash2 m0_hash3 m0_hash4 m0_hash5 m0_hash6 m0_hash7))

; Output round A/E/W state changes
(get-value (a0 e0 m0_w0 m1_w0 m0_a1 m1_a1 m0_e1 m1_e1 m0_w1 m1_w1 m0_a2 m1_a2 m0_e2 m1_e2 m0_w2 m1_w2 m0_a3 m1_a3 m0_e3 m1_e3 m0_w3 m1_w3 m0_a4 m1_a4 m0_e4 m1_e4 m0_w4 m1_w4 m0_a5 m1_a5 m0_e5 m1_e5 m0_w5 m1_w5 m0_a6 m1_a6 m0_e6 m1_e6 m0_w6 m1_w6 m0_a7 m1_a7 m0_e7 m1_e7 m0_w7 m1_w7))
