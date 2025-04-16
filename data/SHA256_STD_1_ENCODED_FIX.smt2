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
; Define K constants
(define-fun k0 () Word #x428a2f98)

; Define H constants (IV/CV)
(define-fun a0 () Word #x6a09e667)
(define-fun b0 () Word #xbb67ae85)
(define-fun c0 () Word #x3c6ef372)
(define-fun d0 () Word #xa54ff53a)
(define-fun e0 () Word #x510e527f)
(define-fun f0 () Word #x9b05688c)
(define-fun g0 () Word #x1f83d9ab)
(define-fun h0 () Word #x5be0cd19)


;; MESSAGE EXPANSION
; MESSAGE 0
; Initial state
(declare-fun m0_w0 () Word)
; Message expansion irrelevant for 1 rounds

; Message Differential (W)
(declare-fun delta_w0 () Word)

; MESSAGE 1 (Derived)
(define-fun m1_w0 () Word (bvxor m0_w0 delta_w0))
; Message expansion assertions irrelevant for 1 rounds


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

; Final state update
(define-fun m0_hash0 () Word (bvadd a0 m0_a1))
(define-fun m1_hash0 () Word (bvadd a0 m1_a1))
(define-fun m0_hash1 () Word (bvadd b0 m0_b1))
(define-fun m1_hash1 () Word (bvadd b0 m1_b1))
(define-fun m0_hash2 () Word (bvadd c0 m0_c1))
(define-fun m1_hash2 () Word (bvadd c0 m1_c1))
(define-fun m0_hash3 () Word (bvadd d0 m0_d1))
(define-fun m1_hash3 () Word (bvadd d0 m1_d1))
(define-fun m0_hash4 () Word (bvadd e0 m0_e1))
(define-fun m1_hash4 () Word (bvadd e0 m1_e1))
(define-fun m0_hash5 () Word (bvadd f0 m0_f1))
(define-fun m1_hash5 () Word (bvadd f0 m1_f1))
(define-fun m0_hash6 () Word (bvadd g0 m0_g1))
(define-fun m1_hash6 () Word (bvadd g0 m1_g1))
(define-fun m0_hash7 () Word (bvadd h0 m0_h1))
(define-fun m1_hash7 () Word (bvadd h0 m1_h1))


;; ASSERTIONS
; Assert messages not the same
(assert
	(distinct delta_w0 #b00000000000000000000000000000000)
)

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
(get-value (a0 e0 m0_w0 m1_w0))
