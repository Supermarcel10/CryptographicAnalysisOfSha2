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
; K constants irrelevant for 0 rounds

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
(define-fun m0_w0 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w1 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w2 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w3 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w4 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w5 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w6 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w7 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w8 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w9 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w10 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w11 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w12 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w13 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w14 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m0_w15 () Word #x0000000000000000) ; Irrelevant for 0 rounds
; Message expansion irrelevant for 0 rounds

; MESSAGE 1
; Initial state
(define-fun m1_w0 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w1 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w2 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w3 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w4 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w5 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w6 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w7 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w8 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w9 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w10 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w11 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w12 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w13 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w14 () Word #x0000000000000000) ; Irrelevant for 0 rounds
(define-fun m1_w15 () Word #x0000000000000000) ; Irrelevant for 0 rounds
; Message expansion irrelevant for 0 rounds


;; MESSAGE COMPRESSION
; MESSAGE 0

; MESSAGE 1

; Final state update
(define-fun m0_hash0 () Word (bvadd a0 a0))
(define-fun m1_hash0 () Word (bvadd a0 a0))
(define-fun m0_hash1 () Word (bvadd b0 b0))
(define-fun m1_hash1 () Word (bvadd b0 b0))
(define-fun m0_hash2 () Word (bvadd c0 c0))
(define-fun m1_hash2 () Word (bvadd c0 c0))
(define-fun m0_hash3 () Word (bvadd d0 d0))
(define-fun m1_hash3 () Word (bvadd d0 d0))
(define-fun m0_hash4 () Word (bvadd e0 e0))
(define-fun m1_hash4 () Word (bvadd e0 e0))
(define-fun m0_hash5 () Word (bvadd f0 f0))
(define-fun m1_hash5 () Word (bvadd f0 f0))
(define-fun m0_hash6 () Word (bvadd g0 g0))
(define-fun m1_hash6 () Word (bvadd g0 g0))
(define-fun m0_hash7 () Word (bvadd h0 h0))
(define-fun m1_hash7 () Word (bvadd h0 h0))


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
(get-value (a0 e0 m0_w0 m1_w0))
