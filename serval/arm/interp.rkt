#lang rosette

; import serval functions with prefix "core:"
(require
  serval/lib/unittest
  rackunit/text-ui
  (prefix-in core:
    (combine-in serval/lib/core
                serval/spec/refinement
                serval/spec/ni))

  (prefix-in rosette:
    rosette/base/core/bitvector)

  ; import Arm AArch64
  "base.rkt"
)

(provide (all-defined-out) (all-from-out "base.rkt"))

#| Library functions |#

; set old[hi:lo] to x
(define (bvinsert hi lo x old)
  (define max (- (bitvector-size (rosette:bv-type old)) 1))
  ; (printf "bvinsert ~a ~a ~a ~a ~a\n" max hi lo x old)
  (assert (>= max hi) "bvinsert: hi out of range")
  (assert (>= hi lo)  "bvinsert: lo out of range")
  (assert (= (+ (- hi lo) 1) (bitvector-size (rosette:bv-type x))) "bvinsert: inserted value wrong size")
  (cond
    [(and (equal? hi max) (equal? lo 0)) x]
    [(equal? hi max) (concat x (extract (- lo 1) 0 old))]
    [(equal? lo   0) (concat (extract max (+ hi 1) old) x)]
    [else            (concat (extract max (+ hi 1) old)
                             x
                             (extract (- lo 1) 0 old))]))

; does x match bitpattern v modulo mask m?
(define (bvmatch? x v m)
  (equal? (bvand x m) v)
)

(define (extend x N signed)
  (if signed (sign-extend x (bitvector N)) (zero-extend x (bitvector N))))

(define (lsl x shift)
  (core:bug-on (< shift 0))
  (bvshl x (min 64 shift)))

(define (lsr x shift)
  (core:bug-on (< shift 0))
  (bvlshr x (min 64 shift)))

(define (asr x shift)
  (core:bug-on (< shift 0))
  (bvashr x (min 64 shift)))

(define (ror x shift)
  (core:bug-on (< shift 0))
  (define shift1 (modulo shift 64))
  (bvor (bvlshr x shift) (bvshl x (- 64 shift1))))

; extract bit i
(define (get-bit i x)
  (extract i i x))

; highest set bit or -1 if all zero
(define (highest-set-bit N x)
  (define (aux i)
    (define i1 (- i 1))
    (cond
      [(equal? i 0)
        -1]
      [(equal? (get-bit i1 x) (bv 1 1))
        i]
      [else
        (aux i1)]))
  (aux N))

(define (count-leading-zero N x)
  (define (aux i)
    (define i1 (- i 1))
    (cond
      [(equal? i 0)
        0]
      [(equal? (get-bit i1 x) (bv 0 1))
        (+ 1 (aux i1))]
      [else
        0]))
  (aux N))

(define (count-leading-sign N x)
  (define s (get-bit (- N 1) x))
  (define (aux i)
    (define i1 (- i 1))
    (cond
      [(equal? i 0)
        0]
      [(equal? (get-bit i1 x) s)
        (+ 1 (aux i1))]
      [else
        0]))
  (aux N))

(define (count-bits N x)
  (define (aux i)
    (define i1 (- i 1))
    (cond
      [(equal? i 0)
        0]
      [(equal? (get-bit i1 x) (bv 1 1))
        (+ 1 (aux i1))]
      [else
        (aux i1)]))
  (aux N))

(define (mkmask M N)
  (concat (bv 0 (- M N)) (bv -1 N)))

(define (ones M)
  (bv -1 M))

(define (zeros M)
  (bv 0 M))

(define (replicate x N)
  (cond
    [(equal? N 0) (bv 0 0)]
    [(equal? N 1) x]
    [else
      (define N2 (/ N 2))
      ; todo: it may be slightly better to split into even-odd and have
      ; even case use a shared copy of (replicate N2 x) for both sides
      (concat (replicate (- N N2) x) (replicate N2 x))]))

(define (is-zero? M x) (equal? x (bv 0 M)))


#| ToyArm Interpreter - very closely based on ToyRISC Interpreter in Serval demo |#

; memory

(struct ptr (block path) #:transparent)

(define/contract (resolve-mem-path cpu sz base offset)
  (-> cpu? (one-of/c 1 2 4 8) bv? bv? ptr?)
  (define mr (core:guess-mregion-from-addr #:dbg current-pc-debug (cpu-mregions cpu) base offset))
  (core:bug-on (equal? mr #f) #:dbg current-pc-debug #:msg (format "Unable to guess mregion for ~a + ~a" base offset))
  (define start (core:mregion-start mr))
  (define end (core:mregion-end mr))
  (define name (core:mregion-name mr))
  (define block (core:mregion-block mr))

  (define addr (bvadd offset base))
  (define size (core:bvpointer sz))
  ; (printf "resolve: ~a+=~a in region ~a ~a..~a = ~a\n" addr size name start end mr)
  (define region-offset (bvsub addr (bv start 64))) ; offset within region

  (core:bug-on (! (core:mregion-inbounds? mr addr size))
                #:dbg current-pc-debug
                #:msg (format "resolve-mem-path: address out of range:\n addr: ~e\n block: ~e" addr name))
  (define path (core:mblock-path block region-offset size #:dbg current-pc-debug))
  (ptr block path))

; memory barriers

(define (data-memory-barrier cpu domain types) #f)
(define (data-synchronization-barrier cpu domain types) #f)

; memory exclusives

(define (aarch64-exclusive-monitors-pass ptr datasize8)
  (core:bug-on #t "todo"))

(define (aarch64-set-exclusive-monitors address datasize8)
  (core:bug-on #t "todo"))

; privileged execution support

(define (aarch64-check-for-svc-trap imm16)
  ; todo
  #f
  )

(define (aarch64-check-for-smc-undef-or-trap imm16)
  ; todo
  #f
  )

(define (aarch64-take-exception level exception return vect-offset)
  (core:bug-on #t "todo"))

(define (aarch64-call-supervisor imm16)
  ; todo: ss-advance
  ; todo: check HRC_EL2.TGE
  (define route-to-el2 #f)
  (define return (bvadd pc (bv 4 64)))
  (define vect-offset (bv 0 64))
  (define exception 'supervisor-call) ; todo: immediate
  (define level
    (cond
      [(bvsgt (cpu-pstate-el cpu) (bv 1 2)) (cpu-pstate-el cpu)]
      [route-to-el2 (bv 2 2)]
      [else (bv 1 2)]))
  (aarch64-take-exception level exception return vect-offset))

(define (aarch64-call-hypervisor cpu imm16)
  ; todo: ss-advance
  (define return (bvadd pc (bv 4 64)))
  (define vect-offset (bv 0 64))
  (define exception 'hypervisor-call) ; todo: immediate
  (define level (if (equal? (cpu-pstate-el cpu) (bv 3 2)) (bv 3 2) (bv 2 2)))
  (aarch64-take-exception level exception return vect-offset))

(define (aarch64-call-secure-monitor imm16)
  ; todo: ss-advance
  (define return (bvadd pc (bv 4 64)))
  (define vect-offset (bv 0 64))
  (define exception 'monitor-call) ; todo: immediate
  (define level (bv 3 2))
  (aarch64-take-exception level exception return vect-offset))

; conditional execution

(define/contract (condition-holds cpu ccode)
  (-> cpu? (bitvector 4) boolean?)
  (define cc (extract 3 1 ccode))
  (define result (cond
    [(equal? cc (bv #b000 3)) (cpu-pstate-z cpu)]
    [(equal? cc (bv #b001 3)) (cpu-pstate-c cpu)]
    [(equal? cc (bv #b010 3)) (cpu-pstate-n cpu)]
    [(equal? cc (bv #b011 3)) (cpu-pstate-v cpu)]
    [(equal? cc (bv #b100 3)) (and (cpu-pstate-c cpu)
                                   (not (cpu-pstate-z cpu)))]
    [(equal? cc (bv #b101 3))
            (equal? (cpu-pstate-n cpu) (cpu-pstate-v cpu))]
    [(equal? cc (bv #b110 3))
            (and (equal? (cpu-pstate-n cpu) (cpu-pstate-v cpu))
                 (not (cpu-pstate-z cpu)))]
    [(equal? cc (bv #b110 3))
            (and (equal? (cpu-pstate-n cpu) (cpu-pstate-v cpu))
                 (not (cpu-pstate-z cpu)))]
    [(equal? cc (bv #b111 3)) #t]
    [else
            (assert #f "condition-holds: incomplete pattern match")]))
  (if (and (equal? (extract 0 0 ccode) (bv #b1 1)) (not (equal? ccode (bv #b1111 4))))
    (not result)
    result
  ))

; shifted register

(define (decode-shift op)
  (cond
    [(equal? op (bv #b00 2)) 'shift-type-lsl]
    [(equal? op (bv #b01 2)) 'shift-type-lsr]
    [(equal? op (bv #b10 2)) 'shift-type-asr]
    [(equal? op (bv #b11 2)) 'shift-type-ror]))

(define (shift-reg cpu reg shifttype amount)
  (define result (cpu-X reg))
  (case shifttype
    [(shift-type-lsl) (lsl result amount)]
    [(shift-type-lsr) (lsr result amount)]
    [(shift-type-asr) (asr result amount)]
    [(shift-type-ror) (ror result amount)]))

; logical immediate values

(define (decode-bit-masks immN imms immr immediate)
  (define len (highest-set-bit (concat immN (bvnot imms))))
  (core:bug-on (< len 1) "UNDEFINED") ; todo
  (core:bug-on (< 6 len)) ; todo: 6 = log2(64), what about M==32?
  (define levels (mkmask 6 len))
  (core:bug-on (&& immediate (equal? (bvand imms levels) levels)) "UNDEFINED") ; todo
  (define S (bitvector->natural (bvand imms levels)))
  (define R (bitvector->natural (bvand immr levels)))
  (define diff (bvsub S R))
  (define tmask_and (bvor  (extract 5 0 diff) (bvnot levels)))
  (define tmask_or  (bvand (extract 5 0 diff) levels))
  (define (tstep i j k prev)
    (bvor
      (bvand
        prev
        (replicate (concat (replicate (extract i i tmask_and) j) (ones j)) k))
      (replicate (concat (zeros j) (replicate (extract i i tmask_or) i)) k)))
  (define tmask0 (ones 64))
  (define tmask1 (tstep 0  1 32 tmask0))
  (define tmask2 (tstep 1  2 16 tmask1))
  (define tmask3 (tstep 2  4  8 tmask2))
  (define tmask4 (tstep 3  8  4 tmask3))
  (define tmask5 (tstep 4 16  2 tmask4))
  (define tmask6 (tstep 5 32  1 tmask5))

  (define wmask_and (bvor  immr (bvnot levels)))
  (define wmask_or  (bvand immr levels))
  (define (wstep i j k prev)
    (bvor
      (bvand
        prev
        (replicate (concat (ones j) (replicate (extract i i wmask_and) i)) k))
      (replicate (concat (replicate (extract i i wmask_or) j) (zeros j)) k)))
  (define wmask0 (zeros 64))
  (define wmask1 (wstep 0  1 32 wmask0))
  (define wmask2 (wstep 1  2 16 wmask1))
  (define wmask3 (wstep 2  4  8 wmask2))
  (define wmask4 (wstep 3  8  4 wmask3))
  (define wmask5 (wstep 4 16  2 wmask4))
  (define wmask6 (wstep 5 32  1 wmask5))

  (define wmask
    (if (equal? (extract 6 6 diff) (bv 1 1))
      (bvand wmask6 tmask6)
      (bvor  wmask6 tmask6)))
  (values wmask tmask6))

; ALU

(define/contract (add-with-carry x y carry-in)
  (-> bv? bv? (bitvector 1)
      (values bv? boolean? boolean? boolean? boolean?))
  (define bv66 (bitvector 66))
  ; (printf "awc ~a ~a ~a\n" x y carry-in)
  (define usum (bvadd (zero-extend x bv66) (zero-extend y bv66) (zero-extend carry-in bv66)))
  (define ssum (bvadd (sign-extend x bv66) (sign-extend y bv66) (zero-extend carry-in bv66)))
  (define result (extract 63 0 usum))
  (define n (equal? (extract 63 63 result) (bv #b1 1)))
  (define z (equal? result (bv 0 64)))
  (define c (not (equal? (zero-extend result bv66) usum)))
  (define v (not (equal? (sign-extend result bv66) ssum)))
  ; (printf "AWC: ~a ~a ~a ~a\n" n z c v)
  (values result n z c v))

(define (add-sub-exec cpu rd operand1 op2 sub_op setflags)
  ; (printf "add-sub\n")
  (define-values (operand2 carry-in)
    (if sub_op
      (values (bvnot op2) (bv #b1 1))
      (values op2         (bv #b0 1))))
  (define-values (result n z c v)
    (add-with-carry operand1 operand2 carry-in))
  ; (printf "addsub: n=~a z=~a c=~a v=~a\n" n z c v)
  (when setflags
    (set-cpu-pstate-n! cpu n)
    (set-cpu-pstate-z! cpu z)
    (set-cpu-pstate-c! cpu c)
    (set-cpu-pstate-v! cpu v))
  (if (and (equal? rd 31) (not setflags))
    (set-cpu-sp! cpu result)
    (set-cpu-X!  cpu rd result)))

; Logical

(define (decode-logical opc)
  (cond
    [(equal? opc (bv #b00 2)) (values 'and #f)]
    [(equal? opc (bv #b01 2)) (values 'orr #f)]
    [(equal? opc (bv #b10 2)) (values 'eor #f)]
    [(equal? opc (bv #b11 2)) (values 'and #t)]))

(define (logical-exec cpu rd op operand1 operand2 setflags datasize8)
  (define result
    (case op
      [(and) (bvand operand1 operand2)]
      [(orr) (bvor  operand1 operand2)]
      [(eor) (bvxor operand1 operand2)]))
  (when setflags
    (set-cpu-pstate-n! cpu (equal? (extract (- (* 8 datasize8) 1) (- (* 8 datasize8) 1) result) (bv 1 1)))
    (set-cpu-pstate-z! cpu (equal? result (bv 0 64)))
    (set-cpu-pstate-c! cpu #f)
    (set-cpu-pstate-v! cpu #f))
  result)

; LD-ST

(define (check-sp-alignment cpu)
  ; todo
  (void))

(define (decode-reg-extend op)
  (cond
    [(equal? op (bv #b000 3)) 'extend-type-uxtb]
    [(equal? op (bv #b001 3)) 'extend-type-uxth]
    [(equal? op (bv #b010 3)) 'extend-type-uxtw]
    [(equal? op (bv #b011 3)) 'extend-type-uxtx]
    [(equal? op (bv #b100 3)) 'extend-type-sxtb]
    [(equal? op (bv #b101 3)) 'extend-type-sxth]
    [(equal? op (bv #b110 3)) 'extend-type-sxtw]
    [(equal? op (bv #b111 3)) 'extend-type-sxtx]))

(define (extend-reg cpu reg exttype shift N)
  (core:bug-on (not (&& (<= 0 shift) (<= shift 4))))
  (define val (cpu-X cpu reg))
  (define-values (unsigned len)
    (case exttype
      [(extend-type-sxtb) (values #f  8)]
      [(extend-type-sxth) (values #f 16)]
      [(extend-type-sxtw) (values #f 32)]
      [(extend-type-sxtx) (values #f 64)]
      [(extend-type-uxtb) (values #t  8)]
      [(extend-type-uxth) (values #t 16)]
      [(extend-type-uxtw) (values #t 32)]
      [(extend-type-uxtx) (values #t 64)]))
  (core:bug-on (not (equal? N 64))) ; todo
  (bvshl (extend (extract (- len 1) 0 val) N unsigned) shift))

(define (ldst-common size opc scale)
  (define datasize8
    (cond ; 8 << scale
      [(equal? scale 0) 1]
      [(equal? scale 1) 2]
      [(equal? scale 2) 4]
      [(equal? scale 3) 8]))
  (cond
    [(equal? opc (bv #b00 2)) (values 'store (if (equal? size (bv #b11 2)) 64 32) #f datasize8)]
    [(equal? opc (bv #b01 2)) (values 'load  (if (equal? size (bv #b11 2)) 64 32) #f datasize8)]
    [else
      (if (equal? size (bv #b11 2))
        (begin
          (core:bug-on (equal? (extract 0 0 opc) (bv 1 1)) "UNDEFINED") ; todo
          (values 'prefetch (void) (void) datasize8))
        (begin ; sign extending load
          (core:bug-on (and (equal? size (bv #b10 2)) (equal? (extract 0 0 opc) (bv 1 1))) "UNDEFINED") ; todo
          (values 'load (if (equal? (extract 0 0 opc) (bv 1 1)) 32 64) #t datasize8)))]))

(define (ldst-exec cpu rd rn memop signed datasize8 offset #:wback wback #:postindex postindex)
  (when (&& (equal? rn 31) (! (equal? memop 'prefetch))) (check-sp-alignment cpu))
  (define address (cpu-XSP cpu rn))
  (define ptr (resolve-mem-path cpu datasize8 address (if postindex (bv 0 64) offset)))
  (case memop
    [(store)
             (define data (extract (- (* 8 datasize8) 1) 0 (cpu-X cpu rd)))
             (core:mblock-istore! (ptr-block ptr) data (ptr-path ptr))]
    [(load)
             (define data (core:mblock-iload (ptr-block ptr) (ptr-path ptr)))
             (set-cpu-X! cpu rd (extend data 64 signed))]
    [(prefetch) (core:bug-on #t "prefetch unsupported")])
  (when wback
    (set-cpu-XSP! cpu rn (bvadd address offset))))

; LDP-STP

(define (ldstp-common opc L imm7)
  (define memop (if (equal? L (bv 1 1)) 'load 'store))
  (core:bug-on (|| (&& (equal? L (bv 0 1)) (equal? (extract 0 0 opc) (bv 1 1)))
                   (equal? opc (bv #b11 2)))
               "UNDEFINED") ; todo
  (define signed (equal? (extract 0 0 opc) (bv 1 1)))
  (define sf     (equal? (extract 1 1 opc) (bv 1 1)))
  (define datasize8 (if sf 4 8))
  (define scale  (if sf 2 3)) ; log2(datasize8)
  (define offset (bvshl (sign-extend imm7 core:i64) scale))
  (values memop signed datasize8 offset))

(define (ldstp-exec cpu rt1 rt2 rn memop signed datasize8 offset #:wback wback #:postindex postindex)
  (when (equal? rn 31) (check-sp-alignment cpu))
  (define address (cpu-XSP cpu rn))
  (define ptr1 (resolve-mem-path cpu datasize8 address (if postindex (bv 0 64) offset)))
  (define ptr2 (resolve-mem-path cpu datasize8 address (bvadd datasize8 (if postindex (bv 0 64) offset))))
  (case memop
    [(store)
             (core:mblock-istore! (ptr-block ptr1) (cpu-X cpu rt1) (ptr-path ptr1))
             (core:mblock-istore! (ptr-block ptr2) (cpu-X cpu rt2) (ptr-path ptr2))]
    [(load)
             (define data1 (core:mblock-iload (ptr-block ptr1) (ptr-path ptr1)))
             (define data2 (core:mblock-iload (ptr-block ptr2) (ptr-path ptr2)))
             (set-cpu-X! cpu rt1 data1)
             (set-cpu-X! cpu rt2 data2)])
  (when wback
    (set-cpu-XSP! cpu rn (bvadd address offset))))


; ISA

; execute one instruction
(define (execute cpu opcode)
  (define pc (cpu-pc cpu))
  ; fields shared by many instructions
  (define sf    (extract 31 31 opcode))
  (define imm12 (extract 21 10 opcode))
  (define rm    (bitvector->natural (extract 20 16 opcode)))
  (define rn    (bitvector->natural (extract  9  5 opcode)))
  (define rd    (bitvector->natural (extract  4  0 opcode)))
  (cond
    ; aarch64_branch_conditional_cond
    [(bvmatch? opcode (bv #b01010100000000000000000000000000 32)
                      (bv #b11111111100000000000000000010000 32))
       (define imm19  (extract 23 05 opcode))
       (define ccode  (extract  3  0 opcode))
       (define offset (sign-extend (concat imm19 (bv 0 2)) 64))
       (if (condition-holds cpu ccode)
         (set-cpu-pc! cpu (bvadd pc offset))
         (set-cpu-pc! cpu (bvadd pc (bv 4 64))))]

    ; aarch64_branch_conditional_compare
    [(bvmatch? opcode (bv #b00110100000000000000000000000000 32)
                      (bv #b01111110000000000000000000000000 32))
       (define op        (extract 24 24 opcode))
       (define imm19     (extract 23 05 opcode))
       (core:bug-on (equal? sf (bv 0 1))) ; todo
       (define datasize8 (if (equal? sf (bv 1 1)) 4 8))  ; todo: not used
       (define iszero    (equal? op (bv 0 1)))
       (define offset    (sign-extend (concat imm19 (bv 0 2)) 64))
       (define operand1  (cpu-X cpu rd))
       (if (equal? (is-zero? 64 operand1) iszero)
         (set-cpu-pc! cpu (bvadd pc offset))
         (set-cpu-pc! cpu (bvadd pc (bv 4 64))))]

    ; aarch64_branch_conditional_test
    [(bvmatch? opcode (bv #b00110110000000000000000000000000 32)
                      (bv #b01111110000000000000000000010000 32))
       (define b5        (extract 31 31 opcode))
       (define op        (extract 24 24 opcode))
       (define b40       (extract 23 19 opcode))
       (define imm14     (extract 18  5 opcode))
       (define datasize8 (if (equal? b5 (bv 1 1)) 4 8))  ; todo: not used
       (define bit-pos   (bitvector->natural (concat b5 b40)))
       (define bit-val   op)
       (define offset    (sign-extend (concat imm14 (bv 0 2)) 64))
       (define operand   (cpu-X cpu rd))
       (if (equal? (get-bit bit-pos operand) bit-val)
         (set-cpu-pc! cpu (bvadd pc offset))
         (set-cpu-pc! cpu (bvadd pc (bv 4 64))))]

    ; aarch64_branch_unconditional_eret

    ; aarch64_branch_unconditional_immediate
    [(bvmatch? opcode (bv #b00010100000000000000000000000000 32)
                      (bv #b01111100000000000000000000000000 32))
       (define op     (extract 31 31 opcode))
       (define imm25  (extract 25  0 opcode))
       (define target (bvadd pc imm25))

       (when (equal? op (bv #b1 1)) (set-cpu-X! cpu 30 (bvadd pc (bv 4 64)))) ; BL
       (set-cpu-pc! cpu target)]

    ; aarch64_branch_unconditional_register
    [(bvmatch? opcode (bv #b11010110000111110000000000000000 32)
                      (bv #b11111111100111111111110000011111 32))
       ; (printf "B.indirect\n")
       (define op (extract 22 21 opcode))
       (cond
         [(equal? op (bv #b00 2)) ; indirect branch
              (define target (cpu-X cpu rn))
              (set-cpu-pc! cpu target)]
         [(equal? op (bv #b01 2)) ; indirect branch and link
              (define target (cpu-X cpu rn))
              (set-cpu-X! cpu 30 (bvadd pc 4))
              (set-cpu-pc! cpu target)]
         [(equal? op (bv #b10 2)) ; return
              ; (printf "RET\n")
              (define target (cpu-X cpu rn))
              (set-cpu-pc! cpu target)]
         [else
              (assert #f "execute/instr/branch-indirect: incomplete pattern match")])]

    ; aarch64_integer_arithmetic_add_sub_extendedreg
    [(bvmatch? opcode (bv #b00001011001000000000000000000000 32)
                      (bv #b00011111111000000000000000000000 32))
       (core:bug-on (equal? sf (bv 0 1)))
       (define op     (extract 30 30 opcode))
       (define S      (extract 29 29 opcode))
       (define option (extract 15 13 opcode))
       (define imm3   (extract 12 10 opcode))
       (define operand1 (cpu-XSP cpu rn))
       (define operand2 (extend-reg rm option imm3))
       (add-sub-exec cpu rd operand1 operand2 (equal? op (bv 1 1)) (equal? S (bv 1 1)))
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_add_sub_immediate
    [(bvmatch? opcode (bv #b00010001000000000000000000000000 32)
                      (bv #b00011111100000000000000000000000 32))
       (core:bug-on (equal? sf (bv 0 1)))
       (define op (extract 30 30 opcode))
       (define S  (extract 29 29 opcode))
       (define sh (extract 20 20 opcode))
       (define operand1 (cpu-XSP cpu rn))
       (define imm
         (if (equal? sh (bv #b01 2))
           (zero-extend (concat imm12 (bv 0 12)) (bitvector 64))
           (zero-extend imm12                    (bitvector 64))))
       (add-sub-exec cpu rd operand1 imm (equal? op (bv 1 1)) (equal? S (bv 1 1)))
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_div
    [(bvmatch? opcode (bv #b0001100110000000000100000000000 32)
                      (bv #b0111111111000001111100000000000 32))
       (core:bug-on (equal? sf (bv 0 1)))
       (define o1     (extract 10 10 opcode))
       (define unsigned (equal? o1 (bv 0 1)))
       (define operand1 (cpu-X cpu rn))
       (define operand2 (cpu-X cpu rm))
       (define result
         (cond
           [(equal? operand2 (bv 0 64)) (bv 0 64)]
           [unsigned (bvudiv operand1 operand2)]
           [else     (bvsdiv operand1 operand2)]))
       (set-cpu-X! cpu result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_address_pc_rel
    [(bvmatch? opcode (bv #b00010000000000000000000000000000 32)
                      (bv #b00011111000000000000000000000000 32))
       (define op    (extract 31 31 opcode))
       (define immlo (extract 30 29 opcode))
       (define immhi (extract 23  5 opcode))
       (define page  (equal? op (bv 1 1)))
       (define imm   (if page
                       (sign-extend (concat immhi immlo (zeros 12)) core:i64)
                       (sign-extend (concat immhi immlo) core:i64)))
       (define base  (if page (concat (extract 63 12 pc) (zeros 12)) pc))
       (set-cpu-X! cpu rd (bvadd base imm))
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_cnt
    [(bvmatch? opcode (bv #b01011010110000000001000000000000 32)
                      (bv #b01111111111111111111100000000000 32))
       (define op (extract 10 10 opcode))
       (define operand (cpu-X cpu rn))
       (define result (if (equal? op (bv 0 1))
            (count-leading-zero 64 operand)
            (count-leading-sign 64 operand)))
       (set-cpu-X! cpu rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_rev
    [(bvmatch? opcode (bv #b01011010110000000000000000000000 32)
                      (bv #b01111111111111111111000000000000 32))
       (define opc      (extract 11 10 opcode))
       (define datasize (if (equal? sf (bv 1 1)) 64 32))
       (define-values (container-size element-size)
         (cond
           [(equal? opc (bv #b00 2)) (values datasize 1)]   ; RBIT
           [(equal? opc (bv #b00 2)) (values 16       8)]   ; REV16
           [(equal? opc (bv #b00 2)) (values 32       8)]   ; REV32
           [(equal? opc (bv #b00 2)) (values 64       8)])) ; REV64
       (core:bug-on (and (equal? opc (bv #b11 2)) (equal? sf (bv 0 1))) "UNDEFINED") ; todo
       (define operand (cpu-X cpu rn))
       ; (define result (elem-reverse operand datasize8 element-size container-size))
       ; (define result (concat (map reverse E) (split C operand)))
       (define result (core:bug-on #t "todo"))
       (set-cpu-X! cpu rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_bitfield
    [(bvmatch? opcode (bv #b00011010110000000001000000000000 32)
                      (bv #b00011111111111111111100000000000 32))
       (define opc   (extract 30 29 opcode))
       (define N     (extract 22 22 opcode))
       (define immr  (extract 21 16 opcode))
       (define imms  (extract 15 10 opcode))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define-values (inzero extend)
         (cond
           [(equal? opc (bv #b00 2)) (values #t #t)] ; SBFM
           [(equal? opc (bv #b01 2)) (values #f #f)] ; BFM
           [(equal? opc (bv #b10 2)) (values #t #f)] ; UBFM
           [(equal? opc (bv #b11 2)) (core:bug-on #t "UNDEFINED")])) ; todo
       (core:bug-on (and (equal? sf (bv 1 1)) (equal? N (bv 0 1))) "UNDEFINED") ; todo
       (core:bug-on (and (equal? sf (bv 0 1))
                         (or (equal? N (bv 0 1))
                             (equal? (get-bit 5 immr) (bv 1 1))
                             (equal? (get-bit 5 imms) (bv 1 1))))
                    "UNDEFINED") ; todo
       (define R (bitvector->natural immr))
       (define S (bitvector->natural imms))
       (define-values (wmask tmask) (decode-bit-masks N imms immr #f))
       (define dst (if inzero (zeros 64) (cpu-X cpu rd)))
       (define src (cpu-X cpu rn))
       (define bot (bvor (bvand (dst         (bvnot wmask)))
                         (bvand ((ror src R) wmask))))
       (define top (if extend (replicate 64 (get-bit S src)) dst))
       (define result (bvor (bvand top (bvnot tmask))
                            (bvand bot tmask)))
       (set-cpu-X! cpu rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_conditional_select
    [(bvmatch? opcode (bv #b00011010100000000000000000000000 32)
                      (bv #b00111111111000000000100000000000 32))
       (define op     (extract 30 30 opcode))
       (define ccode  (extract 15 12 opcode))
       (define op2    (extract 10 10 opcode))
       (define result
         (if (condition-holds cpu ccode)
           (cpu-X cpu rn)
           (begin
             (define res0 (cpu-X cpu rm))
             (define res1 (if (equal? op  (bv #b1 1)) (bvnot res0) res0))
             (define res2 (if (equal? op2 (bv #b1 1)) (bvadd res1 (bv 1 64)) res1))
             res2)))
       (set-cpu-X! cpu rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_logical_immediate
    [(bvmatch? opcode (bv #b00010010000000000000000000000000 32)
                      (bv #b00011111100000000000000000000000 32))
       (define opc   (extract 30 29 opcode))
       (define N     (extract 22 22 opcode))
       (define immr  (extract 21 16 opcode))
       (define imms  (extract 15 10 opcode))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define-values (op setflags) (decode-logical opc))
       (core:bug-on (&& (equal? sf (bv 0 1)) (equal? N (bv 1 1))) "UNDEFINED") ; todo
       (define-values (imm -) (decode-bit-masks N imms immr #t))
       (define operand1 (cpu-X cpu rn))
       (define operand2 imm)
       (define result (logical-exec cpu rd op operand1 operand2 setflags datasize8))
       (if (&& (equal? rd 31) (not setflags))
         (set-cpu-sp! cpu result)
         (set-cpu-X!  cpu rd result))
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_logical_shiftedreg
    [(bvmatch? opcode (bv #b00001010000000000000000000000000 32)
                      (bv #b00011111000000000000000000000000 32))
       (define opc   (extract 30 29 opcode))
       (define shift (extract 23 22 opcode))
       (define N     (extract 21 21 opcode))
       (define imm6  (extract 15 10 opcode))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define-values (op setflags) (decode-logical opc))
       (core:bug-on (&& (equal? sf (bv 0 1)) (equal? (extract 5 5 imm6) (bv 1 1))) "UNDEFINED") ; todo
       (define shift-type (decode-shift shift))
       (define shift-amount (bitvector->natural imm6))
       (define invert (equal? N (bv 1 1)))
       (define operand1 (cpu-X cpu rn))
       (define operand2 (shift-reg cpu rm shift-type shift-amount))
       (define op2 (if invert (bvnot operand2) operand2))
       (define result (logical-exec cpu rd op operand1 operand2 setflags datasize8))
       (set-cpu-X!  cpu rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_ins_ext_insert_movewide
    [(bvmatch? opcode (bv #b00010010100000000000000000000000 32)
                      (bv #b00011111100000000000000000000000 32))
       (define opc   (extract 30 29 opcode))
       (define hw    (extract 22 21 opcode))
       (define imm16 (extract 20  5 opcode))
       (define old (if (equal? opc (bv #b11 2)) (cpu-X cpu rd) (bv 0 64)))
       ; (printf "move-immediate ~a ~a ~a\n" old imm16 hw)
       (define res0 (cond
           [(equal? hw (bv #b00 2)) (bvinsert 15  0 imm16 old)]
           [(equal? hw (bv #b01 2)) (bvinsert 31 16 imm16 old)]
           [(equal? hw (bv #b10 2)) (bvinsert 47 32 imm16 old)]
           [else                    (bvinsert 63 48 imm16 old)]))
       (define result (if (equal? opc (bv #b00 2)) (bvnot res0) res0))
       (set-cpu-X! cpu rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_mul_uniform_add_sub
    [(bvmatch? opcode (bv #b00011011000000000000000000000000 32)
                      (bv #b01111111111000000000000000000000 32))
       (define o0     (extract 15 15 opcode))
       (define ra     (bitvector->natural (extract 14 10 opcode)))
       (define sub-op (equal? o0 (bv 1 1)))
       (define operand1 (cpu-X cpu rn))
       (define operand2 (cpu-X cpu rm))
       (define operand3 (cpu-X cpu ra))
       (define result
         (if sub-op
           (+ operand3 (* operand1 operand2))
           (- operand3 (* operand1 operand2))))
       (set-cpu-X! cpu rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_single_general_immedate_pre/post_idx
    [(bvmatch? opcode (bv #b10111000000000000000010000000000 32)
                      (bv #b10111111001000000000010000000000 32))
       (define size      (extract 31 30 opcode))
       (define opc       (extract 23 22 opcode))
       (define imm9      (extract 20 12 opcode))
       (define postindex (equal? (extract 11 11 opcode) (bv 0 1)))
       (define scale     (bitvector->natural size))
       (define-values (memop signed regsize datasize8) (ldst-common size opc scale))
       (define offset    (sign-extend imm9 core:i64))
       (ldst-exec cpu rd rn memop signed datasize8 offset #:wback #t #:postindex postindex)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_single_general_immedate_unsigned
    [(bvmatch? opcode (bv #b10111001000000000000000000000000 32)
                      (bv #b10111111001000000000000000000000 32))
       (define size      (extract 31 30 opcode))
       (define opc       (extract 23 22 opcode))
       (define imm12     (extract 21 10 opcode))
       (define scale     (bitvector->natural size))
       (define-values (memop signed regsize datasize8) (ldst-common size opc scale))
       (define offset    (bvshl (sign-extend imm12 core:i64) scale))
       (ldst-exec cpu rd rn memop signed datasize8 offset #:wback #f #:postindex #f)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_single_general_register
    [(bvmatch? opcode (bv #b00111000001000000000100000000000 32)
                      (bv #b00111111001000000000110000000000 32))
       (define size        (extract 31 30 opcode))
       (define opc         (extract 23 22 opcode))
       (define option      (extract 15 13 opcode))
       (define S           (extract 12 12 opcode))
       (define scale       (bitvector->natural size))
       (core:bug-on (equal? (extract 1 1 option) (bv 0 1)) "UNDEFINED") ; todo
       (define extend-type (decode-reg-extend option))
       (define shift (if (equal? S (bv 1 1)) scale 0))
       (define-values (memop signed regsize datasize8) (ldst-common size opc scale))
       (define offset (extend-reg cpu rm extend-type shift datasize8))
       (ldst-exec cpu rd rn memop signed datasize8 offset #:wback #f #:postindex #f)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_pair_general_pre/post_idx
    [(bvmatch? opcode (bv #b00101000100000000000000000000000 32)
                      (bv #b00111010100000000000000000000000 32))
       (define opc         (extract 31 30 opcode))
       (define V           (extract 26 26 opcode))
       (define postindex   (equal? (extract 24 24 opcode) (bv 0 1)))
       (define L           (extract 22 22 opcode))
       (define imm7        (extract 21 15 opcode))
       (define rt2         (bitvector->natural (extract 14 10 opcode)))
       (core:bug-on (equal? V (bv 1 1)) "SIMD not supported yet") ; todo
       (define-values (memop signed datasize8 offset) (ldstp-common opc L imm7))
       (ldstp-exec cpu rd rt2 rn memop signed datasize8 offset #:wback #t #:postindex postindex)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_pair_general_offset
    [(bvmatch? opcode (bv #b00101001100000000000000000000000 32)
                      (bv #b00111011100000000000000000000000 32))
       (define opc         (extract 31 30 opcode))
       (define V           (extract 26 26 opcode))
       (define L           (extract 22 22 opcode))
       (define imm7        (extract 21 15 opcode))
       (define rt2         (bitvector->natural (extract 14 10 opcode)))
       (core:bug-on (equal? V (bv 1 1)) "SIMD not supported yet") ; todo
       (define-values (memop signed datasize8 offset) (ldstp-common opc L imm7))
       (ldstp-exec cpu rd rt2 rn memop signed datasize8 offset #:wback #t #:postindex #f)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_exclusive_single
    ; aarch64_memory_exclusive_pair
    [(bvmatch? opcode (bv #b00001000000000000000000000000000 32)
                      (bv #b00111111100000000000000000000000 32))
       (define size        (extract 31 30 opcode))
       (define L           (extract 22 22 opcode))
       (define P           (extract 21 21 opcode))
       (define o0          (extract 15 15 opcode))
       (define rt2         (bitvector->natural (extract 14 10 opcode)))
       (define acctype (if (equal? o0 (bv 1 1)) 'ordered-atomic 'atomic))
       (define pair    (equal? P (bv 1 1)))
       (define memop   (if (equal? L (bv 1 1)) 'load 'store))
       (define elsize8
         (cond ; 1 << size
           [(equal? size 0) 1]
           [(equal? size 1) 2]
           [(equal? size 2) 4]
           [(equal? size 3) 8]))
       (define regsize8 (if (equal? elsize8 8) 8 4))
       (define datasize8 (if pair (* 2 elsize8) elsize8))
       (core:bug-on (and pair (equal? sf (bv 0 1))) "UNDEFINED?") ; todo

       (when (equal? rn 31) (check-sp-alignment cpu))
       (define address (cpu-XSP cpu rn))
       (case memop
         [(store)
                  (define ptr (resolve-mem-path cpu datasize8 address (bv 0 64)))
                  (define data (if pair
                                 (concat (cpu-X cpu rt2) (cpu-X cpu rd))
                                 (cpu-X cpu rd)))
                  (define status
                    (aarch64-exclusive-monitors-pass ptr datasize8))
                  (when status
                    (core:mblock-istore! (ptr-block ptr) data (ptr-path ptr)))
                  (set-cpu-X! cpu rm (if status (bv 0 64) (bv 1 64)))]
         [(load)
                  (aarch64-set-exclusive-monitors address datasize8)
                  (if pair
                    [if (equal? elsize8 4)
                      (begin
                        (define ptr (resolve-mem-path cpu datasize8 address (bv 0 64)))
                        (define data (core:mblock-iload (ptr-block ptr) (ptr-path ptr)))
                        (set-cpu-X! cpu rd  (extract (- (* 8   elsize8) 1)       0 data))
                        (set-cpu-X! cpu rt2 (extract (- (* 8 datasize8) 1) elsize8 data)))
                      (begin
                        ; todo: check 128-bit alignment
                        (define ptr1 (resolve-mem-path cpu datasize8 address (bv 0 64)))
                        (define ptr2 (resolve-mem-path cpu datasize8 address (bv 8 64)))
                        (define data1 (core:mblock-iload (ptr-block ptr1) (ptr-path ptr1)))
                        (define data2 (core:mblock-iload (ptr-block ptr2) (ptr-path ptr2)))
                        (set-cpu-X! cpu rd  data1)
                        (set-cpu-X! cpu rt2 data2))]
                    [begin
                      (define ptr (resolve-mem-path cpu datasize8 address (bv 0 64)))
                      (define data (core:mblock-iload (ptr-block ptr) (ptr-path ptr)))
                      (set-cpu-X! cpu rd (zero-extend data 64))])])
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_ordered
    [(bvmatch? opcode (bv #b00001000100000000000000000000000 32)
                      (bv #b00111111101000000000000000000000 32))
       (define size        (extract 31 30 opcode))
       (define L           (extract 22 22 opcode))
       (define o0          (extract 15 15 opcode))
       (define rt2         (bitvector->natural (extract 14 10 opcode)))
       (define acctype (if (equal? o0 (bv 1 1)) 'limited-ordered 'ordered))
       (define memop   (if (equal? L (bv 1 1)) 'load 'store))
       (define elsize8
         (cond ; 1 << size
           [(equal? size 0) 1]
           [(equal? size 1) 2]
           [(equal? size 2) 4]
           [(equal? size 3) 8]))
       (define regsize8 (if (equal? elsize8 8) 8 4))
       (define datasize8 elsize8)

       (when (equal? rn 31) (check-sp-alignment cpu))
       (define address (cpu-XSP cpu rn))
       (define ptr (resolve-mem-path cpu datasize8 address (bv 0 64)))
       (case memop
         [(store)
                  (define data (cpu-X cpu rd))
                  (core:mblock-istore! (ptr-block ptr) data (ptr-path ptr))]
         [(load)
                  (define data (core:mblock-iload (ptr-block ptr) (ptr-path ptr)))
                  (set-cpu-X! cpu rd (zero-extend data 64))])
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_system_barriers_dmb
    ; aarch64_system_barriers_dsb
    [(bvmatch? opcode (bv #b11010101000000110011000010011111 32)
                      (bv #b11111111111111111111000010011111 32))
     (define CRmh (extract 11 10 opcode))
     (define CRml (extract  9  8 opcode))
     (define opc  (extract  6  5 opcode))
     (core:bug-on (equal? opc (bv 0 2)) "UNDEFINED") ; todo
     (core:bug-on (equal? opc (bv 3 2)) "SB") ; todo
     (define domain
       (cond
         [(equal? CRml (bv 0 2)) 'full_system]
         [(equal? CRmh (bv 0 2)) 'outer-shareable]
         [(equal? CRmh (bv 1 2)) 'non-shareable]
         [(equal? CRmh (bv 2 2)) 'inner-shareable]
         [(equal? CRmh (bv 3 2)) 'full-shareable]))
     (define types
       (cond
         [(equal? CRml (bv 0 2)) 'all]
         [(equal? CRml (bv 1 2)) 'reads]
         [(equal? CRml (bv 2 2)) 'writes]
         [(equal? CRml (bv 3 2)) 'all]))
     (if (equal? opc (bv 1 2))
       (data-memory-barrier cpu domain types)
       (data-synchronization-barrier cpu domain types))
     (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_system_exceptions_runtime_hvc
    ; aarch64_system_exceptions_runtime_smc
    ; aarch64_system_exceptions_runtime_svc
    [(bvmatch? opcode (bv #b11010100000000000000000000000000)
                      (bv #b11111111111000000000000000011100))
       (define imm16 (extract 20  5 opcode))
       (define level (extract  1  0 opcode))
       (core:bug-on (equal? level (bv 0 2)) "UNDEFINED") ; todo
       (cond
         [(equal? level (bv 1 2))
           (aarch64-check-for-svc-trap imm16)
           (aarch64-call-supervisor imm16)]
         [(equal? level (bv 2 2))
           (core:bug-on (equal? (cpu-pstate-el cpu) (bv 0 2)) "UNDEFINED") ; todo: this is missing part of the TrustZone check
           (define hvc-enable #t) ; todo: missing the SCR/HCR check
           (core:bug-on (not hvc-enable) "UNDEFINED") ; todo
           (aarch64-call-hypervisor imm16)]
         [(equal? level (bv 3 2))
           (aarch64-check-for-smc-undef-or-trap imm16)
           (define smc-enable #t) ; todo: missing the SCR check
           (core:bug-on (not smc-enable) "UNDEFINED") ; todo
           (aarch64-call-secure-monitor imm16)])]

    ; aarch64_system_hints
    [(bvmatch? opcode (bv #b11010101000000110010000000011111 32)
                      (bv #b11111111111111111111000000011111 32))
     (define CRm (extract  11  8 opcode))
     (define opc (extract   7  5 opcode))
     (define crop (concat CRm opc))
     (define op
       (cond
         [(equal? crop (bv #b0000000 7)) 'nop]
         [(equal? crop (bv #b0000001 7)) 'yield]
         [(equal? crop (bv #b0000010 7)) 'wfe]
         [(equal? crop (bv #b0000011 7)) 'wfi]
         [(equal? crop (bv #b0000000 7)) 'sev]
         [(equal? crop (bv #b0000001 7)) 'sevl]
         [else ; todo: PAC, BTI, etc.
           'nop]))
     (case op
       [(nop)   #f]
       [(yield) #f] ; todo
       [(wfe)   #f]
       [(wfi)   #f]
       [(sev)   #f]
       [(sevl)  #f])
     (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_system_sysops
    [(bvmatch? opcode (bv #b11010101000010000000000000000000 32)
                      (bv #b11111111110110000000000000000000 32))
     (core:bug-on #t "todo")] ; the only one I want at the moment is DC

    [else
       (assert #f "execute/instr: incomplete pattern match")]
))


; interpret a program from a given cpu state
(define (interpret cpu program)
  ; Use Serval's "split-pc" symbolic optimization
  (core:split-pc (cpu pc) cpu
    (define pc (cpu-pc cpu))
    ; (printf "PC = ~a\n" (cpu-pc cpu))
    ; fetch an instruction to execute
    (cond
      [(hash-has-key? program pc)
        (define insn (hash-ref program pc))
        ; (printf "~a: ~a\n" (bitvector->natural (cpu-pc cpu)) insn)
        (execute cpu insn)
        (interpret cpu program)]
      [else ; illegal address - exit
        ; (printf "End of program at ~a\n" pc)
        (void)])))

; end
