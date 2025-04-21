;; SETUP
(set-option :produce-models true)
(set-logic QF_BV)


;; TYPE
(define-sort Word () (_ BitVec 32))


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
; Define K constant differential
(define-fun delta_k0 () Word #b00000000000000000000000000000000)
(define-fun delta_k1 () Word #b00000000000000000000000000000000)
(define-fun delta_k2 () Word #b00000000000000000000000000000000)
(define-fun delta_k3 () Word #b00000000000000000000000000000000)
(define-fun delta_k4 () Word #b00000000000000000000000000000000)
(define-fun delta_k5 () Word #b00000000000000000000000000000000)
(define-fun delta_k6 () Word #b00000000000000000000000000000000)
(define-fun delta_k7 () Word #b00000000000000000000000000000000)
(define-fun delta_k8 () Word #b00000000000000000000000000000000)

; Define H constant differential (IV/CV)
(define-fun delta_a0 () Word #b00000000000000000000000000000000)
(define-fun delta_b0 () Word #b00000000000000000000000000000000)
(define-fun delta_c0 () Word #b00000000000000000000000000000000)
(define-fun delta_d0 () Word #b00000000000000000000000000000000)
(define-fun delta_e0 () Word #b00000000000000000000000000000000)
(define-fun delta_f0 () Word #b00000000000000000000000000000000)
(define-fun delta_g0 () Word #b00000000000000000000000000000000)
(define-fun delta_h0 () Word #b00000000000000000000000000000000)


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
(declare-fun m0_w7 () Word)
(declare-fun m0_w8 () Word)
; Message expansion irrelevant for 9 rounds

; Message Differential (W)
(declare-fun delta_w0 () Word)
(declare-fun delta_w1 () Word)
(declare-fun delta_w2 () Word)
(declare-fun delta_w3 () Word)
(declare-fun delta_w4 () Word)
(declare-fun delta_w5 () Word)
(declare-fun delta_w6 () Word)
(declare-fun delta_w7 () Word)
(declare-fun delta_w8 () Word)

; MESSAGE 1 (Derived)
(define-fun m1_w0 () Word (bvxor m0_w0 delta_w0))
(define-fun m1_w1 () Word (bvxor m0_w1 delta_w1))
(define-fun m1_w2 () Word (bvxor m0_w2 delta_w2))
(define-fun m1_w3 () Word (bvxor m0_w3 delta_w3))
(define-fun m1_w4 () Word (bvxor m0_w4 delta_w4))
(define-fun m1_w5 () Word (bvxor m0_w5 delta_w5))
(define-fun m1_w6 () Word (bvxor m0_w6 delta_w6))
(define-fun m1_w7 () Word (bvxor m0_w7 delta_w7))
(define-fun m1_w8 () Word (bvxor m0_w8 delta_w8))
; Message expansion assertions irrelevant for 9 rounds


;; MESSAGE COMPRESSION
(define-fun delta_t1_1 () Word (t1 delta_h0 delta_e0 delta_f0 delta_g0 delta_k0 delta_w0))
(define-fun delta_t2_1 () Word (t2 delta_a0 delta_b0 delta_c0))
(define-fun delta_a1 () Word (bvadd delta_t1_1 delta_t2_1))
(define-fun delta_b1 () Word delta_a0)
(define-fun delta_c1 () Word delta_b0)
(define-fun delta_d1 () Word delta_c0)
(define-fun delta_e1 () Word (bvadd delta_d0 delta_t1_1))
(define-fun delta_f1 () Word delta_e0)
(define-fun delta_g1 () Word delta_f0)
(define-fun delta_h1 () Word delta_g0)
(define-fun delta_t1_2 () Word (t1 delta_h1 delta_e1 delta_f1 delta_g1 delta_k1 delta_w1))
(define-fun delta_t2_2 () Word (t2 delta_a1 delta_b1 delta_c1))
(define-fun delta_a2 () Word (bvadd delta_t1_2 delta_t2_2))
(define-fun delta_b2 () Word delta_a1)
(define-fun delta_c2 () Word delta_b1)
(define-fun delta_d2 () Word delta_c1)
(define-fun delta_e2 () Word (bvadd delta_d1 delta_t1_2))
(define-fun delta_f2 () Word delta_e1)
(define-fun delta_g2 () Word delta_f1)
(define-fun delta_h2 () Word delta_g1)
(define-fun delta_t1_3 () Word (t1 delta_h2 delta_e2 delta_f2 delta_g2 delta_k2 delta_w2))
(define-fun delta_t2_3 () Word (t2 delta_a2 delta_b2 delta_c2))
(define-fun delta_a3 () Word (bvadd delta_t1_3 delta_t2_3))
(define-fun delta_b3 () Word delta_a2)
(define-fun delta_c3 () Word delta_b2)
(define-fun delta_d3 () Word delta_c2)
(define-fun delta_e3 () Word (bvadd delta_d2 delta_t1_3))
(define-fun delta_f3 () Word delta_e2)
(define-fun delta_g3 () Word delta_f2)
(define-fun delta_h3 () Word delta_g2)
(define-fun delta_t1_4 () Word (t1 delta_h3 delta_e3 delta_f3 delta_g3 delta_k3 delta_w3))
(define-fun delta_t2_4 () Word (t2 delta_a3 delta_b3 delta_c3))
(define-fun delta_a4 () Word (bvadd delta_t1_4 delta_t2_4))
(define-fun delta_b4 () Word delta_a3)
(define-fun delta_c4 () Word delta_b3)
(define-fun delta_d4 () Word delta_c3)
(define-fun delta_e4 () Word (bvadd delta_d3 delta_t1_4))
(define-fun delta_f4 () Word delta_e3)
(define-fun delta_g4 () Word delta_f3)
(define-fun delta_h4 () Word delta_g3)
(define-fun delta_t1_5 () Word (t1 delta_h4 delta_e4 delta_f4 delta_g4 delta_k4 delta_w4))
(define-fun delta_t2_5 () Word (t2 delta_a4 delta_b4 delta_c4))
(define-fun delta_a5 () Word (bvadd delta_t1_5 delta_t2_5))
(define-fun delta_b5 () Word delta_a4)
(define-fun delta_c5 () Word delta_b4)
(define-fun delta_d5 () Word delta_c4)
(define-fun delta_e5 () Word (bvadd delta_d4 delta_t1_5))
(define-fun delta_f5 () Word delta_e4)
(define-fun delta_g5 () Word delta_f4)
(define-fun delta_h5 () Word delta_g4)
(define-fun delta_t1_6 () Word (t1 delta_h5 delta_e5 delta_f5 delta_g5 delta_k5 delta_w5))
(define-fun delta_t2_6 () Word (t2 delta_a5 delta_b5 delta_c5))
(define-fun delta_a6 () Word (bvadd delta_t1_6 delta_t2_6))
(define-fun delta_b6 () Word delta_a5)
(define-fun delta_c6 () Word delta_b5)
(define-fun delta_d6 () Word delta_c5)
(define-fun delta_e6 () Word (bvadd delta_d5 delta_t1_6))
(define-fun delta_f6 () Word delta_e5)
(define-fun delta_g6 () Word delta_f5)
(define-fun delta_h6 () Word delta_g5)
(define-fun delta_t1_7 () Word (t1 delta_h6 delta_e6 delta_f6 delta_g6 delta_k6 delta_w6))
(define-fun delta_t2_7 () Word (t2 delta_a6 delta_b6 delta_c6))
(define-fun delta_a7 () Word (bvadd delta_t1_7 delta_t2_7))
(define-fun delta_b7 () Word delta_a6)
(define-fun delta_c7 () Word delta_b6)
(define-fun delta_d7 () Word delta_c6)
(define-fun delta_e7 () Word (bvadd delta_d6 delta_t1_7))
(define-fun delta_f7 () Word delta_e6)
(define-fun delta_g7 () Word delta_f6)
(define-fun delta_h7 () Word delta_g6)
(define-fun delta_t1_8 () Word (t1 delta_h7 delta_e7 delta_f7 delta_g7 delta_k7 delta_w7))
(define-fun delta_t2_8 () Word (t2 delta_a7 delta_b7 delta_c7))
(define-fun delta_a8 () Word (bvadd delta_t1_8 delta_t2_8))
(define-fun delta_b8 () Word delta_a7)
(define-fun delta_c8 () Word delta_b7)
(define-fun delta_d8 () Word delta_c7)
(define-fun delta_e8 () Word (bvadd delta_d7 delta_t1_8))
(define-fun delta_f8 () Word delta_e7)
(define-fun delta_g8 () Word delta_f7)
(define-fun delta_h8 () Word delta_g7)
(define-fun delta_t1_9 () Word (t1 delta_h8 delta_e8 delta_f8 delta_g8 delta_k8 delta_w8))
(define-fun delta_t2_9 () Word (t2 delta_a8 delta_b8 delta_c8))
(define-fun delta_a9 () Word (bvadd delta_t1_9 delta_t2_9))
(define-fun delta_b9 () Word delta_a8)
(define-fun delta_c9 () Word delta_b8)
(define-fun delta_d9 () Word delta_c8)
(define-fun delta_e9 () Word (bvadd delta_d8 delta_t1_9))
(define-fun delta_f9 () Word delta_e8)
(define-fun delta_g9 () Word delta_f8)
(define-fun delta_h9 () Word delta_g8)

; Final state difference
(define-fun delta_hash0 () Word (bvadd delta_a0 delta_a9))
(define-fun delta_hash1 () Word (bvadd delta_b0 delta_b9))
(define-fun delta_hash2 () Word (bvadd delta_c0 delta_c9))
(define-fun delta_hash3 () Word (bvadd delta_d0 delta_d9))
(define-fun delta_hash4 () Word (bvadd delta_e0 delta_e9))
(define-fun delta_hash5 () Word (bvadd delta_f0 delta_f9))
(define-fun delta_hash6 () Word (bvadd delta_g0 delta_g9))
(define-fun delta_hash7 () Word (bvadd delta_h0 delta_h9))


;; ASSERTIONS
; Assert messages not the same
(assert (or
	(distinct delta_w0 #b00000000000000000000000000000000)
	(distinct delta_w1 #b00000000000000000000000000000000)
	(distinct delta_w2 #b00000000000000000000000000000000)
	(distinct delta_w3 #b00000000000000000000000000000000)
	(distinct delta_w4 #b00000000000000000000000000000000)
	(distinct delta_w5 #b00000000000000000000000000000000)
	(distinct delta_w6 #b00000000000000000000000000000000)
	(distinct delta_w7 #b00000000000000000000000000000000)
	(distinct delta_w8 #b00000000000000000000000000000000)
))

; Assert difference in output hash is none
(assert (and
	(= delta_hash0 #b00000000000000000000000000000000)
	(= delta_hash1 #b00000000000000000000000000000000)
	(= delta_hash2 #b00000000000000000000000000000000)
	(= delta_hash3 #b00000000000000000000000000000000)
	(= delta_hash4 #b00000000000000000000000000000000)
	(= delta_hash5 #b00000000000000000000000000000000)
	(= delta_hash6 #b00000000000000000000000000000000)
	(= delta_hash7 #b00000000000000000000000000000000)
))


;; GO!
(check-sat)


;; GET OUTPUT
; Input message
(get-value (m0_w0 m1_w0 m0_w1 m1_w1 m0_w2 m1_w2 m0_w3 m1_w3 m0_w4 m1_w4 m0_w5 m1_w5 m0_w6 m1_w6 m0_w7 m1_w7))

; Output round A/E/W state changes
(get-value (delta_a0 delta_e0 delta_w0 delta_a1 delta_e1 delta_w1 delta_a2 delta_e2 delta_w2 delta_a3 delta_e3 delta_w3 delta_a4 delta_e4 delta_w4 delta_a5 delta_e5 delta_w5 delta_a6 delta_e6 delta_w6 delta_a7 delta_e7 delta_w7 delta_a8 delta_e8 delta_w8))
