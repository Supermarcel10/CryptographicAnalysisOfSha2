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
; Message expansion irrelevant for 3 rounds

; Message Differential (W)
(declare-fun delta_w0 () Word)
(declare-fun delta_w1 () Word)
(declare-fun delta_w2 () Word)

; MESSAGE 1 (Derived)
(define-fun m1_w0 () Word (bvxor m0_w0 delta_w0))
(define-fun m1_w1 () Word (bvxor m0_w1 delta_w1))
(define-fun m1_w2 () Word (bvxor m0_w2 delta_w2))
; Message expansion assertions irrelevant for 3 rounds


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

; Final state difference
(define-fun delta_hash0 () Word (bvadd delta_a0 delta_a3))
(define-fun delta_hash1 () Word (bvadd delta_b0 delta_b3))
(define-fun delta_hash2 () Word (bvadd delta_c0 delta_c3))
(define-fun delta_hash3 () Word (bvadd delta_d0 delta_d3))
(define-fun delta_hash4 () Word (bvadd delta_e0 delta_e3))
(define-fun delta_hash5 () Word (bvadd delta_f0 delta_f3))
(define-fun delta_hash6 () Word (bvadd delta_g0 delta_g3))
(define-fun delta_hash7 () Word (bvadd delta_h0 delta_h3))


;; ASSERTIONS
; Assert messages not the same
(assert (or
	(distinct delta_w0 #b00000000000000000000000000000000)
	(distinct delta_w1 #b00000000000000000000000000000000)
	(distinct delta_w2 #b00000000000000000000000000000000)
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
(get-value (m0_w0 m1_w0 m0_w1 m1_w1 m0_w2 m1_w2))

; Output round A/E/W state changes
(get-value (delta_a0 delta_e0 delta_w0 delta_a1 delta_e1 delta_w1 delta_a2 delta_e2 delta_w2))
