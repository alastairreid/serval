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
  "memory.rkt"
  "system.rkt"
)

(provide
  (all-defined-out)
  (all-from-out "base.rkt")
  (all-from-out "memory.rkt")
  (all-from-out "system.rkt"))


#| ToyArm Interpreter - very closely based on ToyRISC Interpreter in Serval demo |#

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
            (core:bug-on #f #:msg "condition-holds: incomplete pattern match")]))
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

(define (shift-reg cpu N reg shifttype amount)
  (define result (cpu-X cpu N reg))
  (case shifttype
    [(shift-type-lsl) (lsl result amount)]
    [(shift-type-lsr) (lsr result amount)]
    [(shift-type-asr) (asr result amount)]
    [(shift-type-ror) (ror result amount)]))

; logical immediate values

(define (decode-bit-masks M immN imms immr immediate)
  (core:bug-on (! (equal? M 64)))
  (define len (highest-set-bit (concat immN (bvnot imms))))
  (core:bug-on (< len 1) #:msg "UNDEFINED") ; todo
  (core:bug-on (< 6 len)) ; todo: 6 = log2(64), what about M==32?
  (define levels (mkmask 6 len))
  (core:bug-on (&& immediate (equal? (bvand imms levels) levels)) #:msg "UNDEFINED") ; todo
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

(define/contract (add-with-carry N x y carry-in)
  (-> integer? bv? bv? (bitvector 1)
      (values bv? boolean? boolean? boolean? boolean?))
  (define bv66 (bitvector 66))
  ; (printf "awc ~a ~a ~a\n" x y carry-in)
  (define usum (bvadd (zero-extend x bv66) (zero-extend y bv66) (zero-extend carry-in bv66)))
  (define ssum (bvadd (sign-extend x bv66) (sign-extend y bv66) (zero-extend carry-in bv66)))
  (define result (extract (- N 1) 0 usum))
  (define n (equal? (get-bit (- N 1) result) (bv #b1 1)))
  (define z (equal? result (bv 0 N)))
  (define c (not (equal? (zero-extend result bv66) usum)))
  (define v (not (equal? (sign-extend result bv66) ssum)))
  ; (printf "AWC: ~a ~a ~a ~a\n" n z c v)
  (values result n z c v))

(define (add-sub-exec cpu N rd operand1 op2 sub_op setflags)
  ; (printf "add-sub\n")
  (define-values (operand2 carry-in)
    (if sub_op
      (values (bvnot op2) (bv #b1 1))
      (values op2         (bv #b0 1))))
  (define-values (result n z c v)
    (add-with-carry N operand1 operand2 carry-in))
  ; (printf "addsub: n=~a z=~a c=~a v=~a\n" n z c v)
  (when setflags
    (set-cpu-pstate-n! cpu n)
    (set-cpu-pstate-z! cpu z)
    (set-cpu-pstate-c! cpu c)
    (set-cpu-pstate-v! cpu v))
  (if (and (equal? rd 31) (not setflags))
    (set-cpu-sp! cpu N result)
    (set-cpu-X!  cpu N rd result)))

; Logical

(define (decode-logical opc)
  (cond
    [(equal? opc (bv #b00 2)) (values 'and #f)]
    [(equal? opc (bv #b01 2)) (values 'orr #f)]
    [(equal? opc (bv #b10 2)) (values 'eor #f)]
    [(equal? opc (bv #b11 2)) (values 'and #t)]))

(define (logical-exec cpu N rd op operand1 operand2 setflags)
  (define result
    (case op
      [(and) (bvand operand1 operand2)]
      [(orr) (bvor  operand1 operand2)]
      [(eor) (bvxor operand1 operand2)]))
  (when setflags
    (set-cpu-pstate-n! cpu (equal? (extract (- N 1) (- N 1) result) (bv 1 1)))
    (set-cpu-pstate-z! cpu (equal? result (bv 0 N)))
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

(define (extend-reg cpu N reg exttype shift)
  (core:bug-on (not (&& (<= 0 shift) (<= shift 4))))
  (define val (cpu-X cpu N reg))
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
  (define len1 (min len (- N shift)))
  (bvshl (extend (extract (- len1 1) 0 val) N unsigned) shift))

(define (ldst-common size opc scale)
  (define datasize8
    (cond ; 8 << scale
      [(equal? scale 0) 1]
      [(equal? scale 1) 2]
      [(equal? scale 2) 4]
      [(equal? scale 3) 8]))
  (cond
    [(equal? opc (bv #b00 2)) (values 'store #f (if (equal? size (bv #b11 2)) 64 32) datasize8)]
    [(equal? opc (bv #b01 2)) (values 'load  #f (if (equal? size (bv #b11 2)) 64 32) datasize8)]
    [else
      (if (equal? size (bv #b11 2))
        (begin
          (core:bug-on (equal? (extract 0 0 opc) (bv 1 1)) #:msg "UNDEFINED") ; todo
          (values 'prefetch (void) (void) datasize8))
        (begin ; sign extending load
          (core:bug-on (and (equal? size (bv #b10 2)) (equal? (extract 0 0 opc) (bv 1 1))) #:msg "UNDEFINED") ; todo
          (values 'load
                  #t
                  (if (equal? (extract 0 0 opc) (bv 1 1)) 32 64)
                  datasize8)))]))

(define/contract (ldst-exec cpu rd rn memop signed datasize8 regsize offset #:wback wback #:postindex postindex)
  (-> cpu? integer? integer? (one-of/c 'prefetch 'store 'load) boolean? (one-of/c 1 2 4 8) (one-of/c 32 64) (bitvector 64) #:wback boolean? #:postindex boolean? void?)
  (when (&& (equal? rn 31) (! (equal? memop 'prefetch))) (check-sp-alignment cpu))
  (define address (cpu-XSP cpu 64 rn))
  (define datasize (* 8 datasize8))
  (case memop
    [(store)
             (define data (cpu-X cpu datasize rd))
             (mem-write! cpu datasize8 address (if postindex (bv 0 64) offset) data)]
    [(load)
             (define data (mem-read cpu datasize8 address (if postindex (bv 0 64) offset)))
             (set-cpu-X! cpu regsize rd (extend data regsize signed))]
    [(prefetch) (core:bug-on #t #:msg "prefetch unsupported")])
  (when wback
    (set-cpu-XSP! cpu 64 rn (bvadd address offset))))

; LDP-STP

(define (ldstp-common opc L imm7)
  (define memop (if (equal? L (bv 1 1)) 'load 'store))
  (core:bug-on (|| (&& (equal? L (bv 0 1)) (equal? (extract 0 0 opc) (bv 1 1)))
                   (equal? opc (bv #b11 2)))
               #:msg "UNDEFINED") ; todo
  (define signed (equal? (extract 0 0 opc) (bv 1 1)))
  (define sf     (equal? (extract 1 1 opc) (bv 1 1)))
  (define datasize8 (if sf 8 4))
  (define scale  (bv (if sf 3 2) 64)) ; log2(datasize8)
  (define offset (bvshl (sign-extend imm7 core:i64) scale))
  ; (printf "ldstp ~a ~a ~a ~a\n" memop signed datasize8 offset)
  (values memop signed datasize8 offset))

(define (ldstp-exec cpu rt1 rt2 rn memop signed datasize8 offset #:wback wback #:postindex postindex)
  (when (equal? rn 31) (check-sp-alignment cpu))
  (define address (cpu-XSP cpu 64 rn))
  (define datasize (* 8 datasize8))
  (case memop
    [(store)
             (mem-write! cpu datasize8 address (if postindex (bv 0 64) offset) (cpu-X cpu datasize rt1))
             (mem-write! cpu datasize8 address (bvadd (core:bvpointer datasize8) (if postindex (bv 0 64) offset)) (cpu-X cpu datasize rt2))]
    [(load)
             (define data1 (mem-read cpu datasize8 address (if postindex (bv 0 64) offset)))
             (define data2 (mem-read cpu datasize8 address (bvadd (core:bvpointer datasize8) (if postindex (bv 0 64) offset))))
             (set-cpu-X! cpu datasize rt1 data1)
             (set-cpu-X! cpu datasize rt2 data2)])
  (when wback
    (set-cpu-XSP! cpu 64 rn (bvadd address offset))))


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
       (define offset (sign-extend (concat imm19 (bv 0 2)) core:i64))
       (if (condition-holds cpu ccode)
         (set-cpu-pc! cpu (bvadd pc offset))
         (set-cpu-pc! cpu (bvadd pc (bv 4 64))))]

    ; aarch64_branch_conditional_compare
    [(bvmatch? opcode (bv #b00110100000000000000000000000000 32)
                      (bv #b01111110000000000000000000000000 32))
       (define op        (extract 24 24 opcode))
       (define imm19     (extract 23 05 opcode))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define datasize  (* 8 datasize8))
       (define iszero    (equal? op (bv 0 1)))
       (define offset    (sign-extend (concat imm19 (bv 0 2)) core:i64))
       (define operand1  (cpu-X cpu datasize rd))
       (if (equal? (is-zero? datasize operand1) iszero)
         (set-cpu-pc! cpu (bvadd pc offset))
         (set-cpu-pc! cpu (bvadd pc (bv 4 64))))]

    ; aarch64_branch_conditional_test
    [(bvmatch? opcode (bv #b00110110000000000000000000000000 32)
                      (bv #b01111110000000000000000000010000 32))
       (define b5        (extract 31 31 opcode))
       (define op        (extract 24 24 opcode))
       (define b40       (extract 23 19 opcode))
       (define imm14     (extract 18  5 opcode))
       (define datasize8 (if (equal? b5 (bv 1 1)) 4 8))
       (define datasize  (* 8 datasize8))
       (define bit-pos   (bitvector->natural (concat b5 b40)))
       (define bit-val   op)
       (define offset    (sign-extend (concat imm14 (bv 0 2)) core:i64))
       (define operand   (cpu-X cpu datasize rd))
       (if (equal? (get-bit bit-pos operand) bit-val)
         (set-cpu-pc! cpu (bvadd pc offset))
         (set-cpu-pc! cpu (bvadd pc (bv 4 64))))]

    ; aarch64_branch_unconditional_eret

    ; aarch64_branch_unconditional_immediate
    [(bvmatch? opcode (bv #b00010100000000000000000000000000 32)
                      (bv #b01111100000000000000000000000000 32))
       (define op     (extract 31 31 opcode))
       (define imm25  (extract 25  0 opcode))
       (define target (bvadd pc (sign-extend imm25 core:i64)))

       (when (equal? op (bv #b1 1)) (set-cpu-X! cpu 64 30 (bvadd pc (bv 4 64)))) ; BL
       (set-cpu-pc! cpu target)]

    ; aarch64_branch_unconditional_register
    [(bvmatch? opcode (bv #b11010110000111110000000000000000 32)
                      (bv #b11111111100111111111110000011111 32))
       ; (printf "B.indirect\n")
       (define op (extract 22 21 opcode))
       (cond
         [(equal? op (bv #b00 2)) ; indirect branch
              (define target (cpu-X cpu 64 rn))
              (set-cpu-pc! cpu target)]
         [(equal? op (bv #b01 2)) ; indirect branch and link
              (define target (cpu-X cpu 64 rn))
              (set-cpu-X! cpu 64 30 (bvadd pc 4))
              (set-cpu-pc! cpu target)]
         [(equal? op (bv #b10 2)) ; return
              ; (printf "RET\n")
              (define target (cpu-X cpu 64 rn))
              (set-cpu-pc! cpu target)]
         [else
              (core:bug-on #f #:msg "execute/instr/branch-indirect: incomplete pattern match")])]

    ; aarch64_integer_arithmetic_add_sub_extendedreg
    [(bvmatch? opcode (bv #b00001011001000000000000000000000 32)
                      (bv #b00011111111000000000000000000000 32))
       (define op     (extract 30 30 opcode))
       (define S      (extract 29 29 opcode))
       (define option (extract 15 13 opcode))
       (define imm3   (extract 12 10 opcode))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define datasize (* 8 datasize8))
       (define operand1 (cpu-XSP cpu datasize rn))
       (define operand2 (extend-reg cpu datasize rm option imm3))
       (add-sub-exec cpu datasize rd operand1 operand2 (equal? op (bv 1 1)) (equal? S (bv 1 1)))
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_add_sub_immediate
    [(bvmatch? opcode (bv #b00010001000000000000000000000000 32)
                      (bv #b00011111100000000000000000000000 32))
       (define op (extract 30 30 opcode))
       (define S  (extract 29 29 opcode))
       (define sh (extract 20 20 opcode))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define datasize (* 8 datasize8))
       (define operand1 (cpu-XSP cpu datasize rn))
       (define imm
         (if (equal? sh (bv #b01 2))
           (zero-extend (concat imm12 (bv 0 12)) (bitvector datasize))
           (zero-extend imm12                    (bitvector datasize))))
       (add-sub-exec cpu datasize rd operand1 imm (equal? op (bv 1 1)) (equal? S (bv 1 1)))
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_div
    [(bvmatch? opcode (bv #b0001100110000000000100000000000 32)
                      (bv #b0111111111000001111100000000000 32))
       (define o1     (extract 10 10 opcode))
       (define unsigned (equal? o1 (bv 0 1)))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define datasize (* 8 datasize8))
       (define operand1 (cpu-X cpu datasize rn))
       (define operand2 (cpu-X cpu datasize rm))
       (define result
         (cond
           [(equal? operand2 (bv 0 datasize)) (bv 0 datasize)]
           [unsigned (bvudiv operand1 operand2)]
           [else     (bvsdiv operand1 operand2)]))
       (set-cpu-X! cpu datasize result)
       (set-cpu-pc! cpu 64 (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_address_pc_rel
    [(bvmatch? opcode (bv #b00010000000000000000000000000000 32)
                      (bv #b00011111000000000000000000000000 32))
       (define op    (extract 31 31 opcode))
       (define immlo (extract 30 29 opcode))
       (define immhi (extract 23  5 opcode))
       (define page  (equal? op (bv 1 1)))
       (define imm   (if page
                       (sign-extend (concat immhi immlo (zeros 12)) core:i64)
                       (sign-extend (concat immhi immlo)            core:i64)))
       (define base  (if page (concat (extract 63 12 pc) (zeros 12)) pc))
       (set-cpu-X!  cpu 64 rd (bvadd base imm))
       (set-cpu-pc! cpu 64 (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_cnt
    [(bvmatch? opcode (bv #b01011010110000000001000000000000 32)
                      (bv #b01111111111111111111100000000000 32))
       (define op (extract 10 10 opcode))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define datasize (* 8 datasize8))
       (define operand (cpu-X cpu datasize rn))
       (define result (if (equal? op (bv 0 1))
            (count-leading-zero datasize operand)
            (count-leading-sign datasize operand)))
       (set-cpu-X! cpu datasize rd result)
       (set-cpu-pc! cpu 64 (bvadd pc (bv 4 64)))]

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
       (core:bug-on (and (equal? opc (bv #b11 2)) (equal? sf (bv 0 1))) #:msg "UNDEFINED") ; todo
       (define operand (cpu-X cpu datasize rn))
       ; (define result (elem-reverse operand datasize8 element-size container-size))
       ; (define result (concat (map reverse E) (split C operand)))
       (define result (core:bug-on #t #:msg "todo"))
       (set-cpu-X! cpu datasize rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_bitfield
    [(bvmatch? opcode (bv #b00011010110000000001000000000000 32)
                      (bv #b00011111111111111111100000000000 32))
       (define opc   (extract 30 29 opcode))
       (define N     (extract 22 22 opcode))
       (define immr  (extract 21 16 opcode))
       (define imms  (extract 15 10 opcode))
       (define datasize (if (equal? sf (bv 1 1)) 62 32))
       (define-values (inzero extend)
         (cond
           [(equal? opc (bv #b00 2)) (values #t #t)] ; SBFM
           [(equal? opc (bv #b01 2)) (values #f #f)] ; BFM
           [(equal? opc (bv #b10 2)) (values #t #f)] ; UBFM
           [(equal? opc (bv #b11 2)) (core:bug-on #t #:msg "UNDEFINED")])) ; todo
       (core:bug-on (and (equal? sf (bv 1 1)) (equal? N (bv 0 1))) #:msg "UNDEFINED") ; todo
       (core:bug-on (and (equal? sf (bv 0 1))
                         (or (equal? N (bv 0 1))
                             (equal? (get-bit 5 immr) (bv 1 1))
                             (equal? (get-bit 5 imms) (bv 1 1))))
                    #:msg "UNDEFINED") ; todo
       (define R (bitvector->natural immr))
       (define S (bitvector->natural imms))
       (define-values (wmask tmask) (decode-bit-masks datasize N imms immr #f))
       (define dst (if inzero (zeros 64) (cpu-X cpu datasize rd)))
       (define src (cpu-X cpu datasize rn))
       (define bot (bvor (bvand (dst         (bvnot wmask)))
                         (bvand ((ror src R) wmask))))
       (define top (if extend (replicate 64 (get-bit S src)) dst))
       (define result (bvor (bvand top (bvnot tmask))
                            (bvand bot tmask)))
       (set-cpu-X!  cpu datasize rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_conditional_select
    [(bvmatch? opcode (bv #b00011010100000000000000000000000 32)
                      (bv #b00111111111000000000100000000000 32))
       (define op     (extract 30 30 opcode))
       (define ccode  (extract 15 12 opcode))
       (define op2    (extract 10 10 opcode))
       (define datasize (if (equal? sf (bv 1 1)) 64 32))
       (define result
         (if (condition-holds cpu ccode)
           (cpu-X cpu datasize rn)
           (begin
             (define res0 (cpu-X cpu datasize rm))
             (define res1 (if (equal? op  (bv #b1 1)) (bvnot res0) res0))
             (define res2 (if (equal? op2 (bv #b1 1)) (bvadd res1 (bv 1 64)) res1))
             res2)))
       (set-cpu-X! cpu datasize rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_logical_immediate
    [(bvmatch? opcode (bv #b00010010000000000000000000000000 32)
                      (bv #b00011111100000000000000000000000 32))
       (define opc   (extract 30 29 opcode))
       (define N     (extract 22 22 opcode))
       (define immr  (extract 21 16 opcode))
       (define imms  (extract 15 10 opcode))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define datasize  (* 8 datasize8))
       (define-values (op setflags) (decode-logical opc))
       (core:bug-on (&& (equal? sf (bv 0 1)) (equal? N (bv 1 1))) #:msg "UNDEFINED") ; todo
       (define-values (imm -) (decode-bit-masks N imms immr #t))
       (define operand1 (cpu-X cpu datasize rn))
       (define operand2 imm)
       (define result (logical-exec cpu datasize rd op operand1 operand2 setflags))
       (if (&& (equal? rd 31) (not setflags))
         (set-cpu-sp! cpu (zero-extend result core:i64))
         (set-cpu-X!  cpu datasize rd result))
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_logical_shiftedreg
    [(bvmatch? opcode (bv #b00001010000000000000000000000000 32)
                      (bv #b00011111000000000000000000000000 32))
       (define opc   (extract 30 29 opcode))
       (define shift (extract 23 22 opcode))
       (define N     (extract 21 21 opcode))
       (define imm6  (extract 15 10 opcode))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define datasize  (* 8 datasize8))
       (define-values (op setflags) (decode-logical opc))
       (core:bug-on (&& (equal? sf (bv 0 1)) (equal? (extract 5 5 imm6) (bv 1 1))) #:msg "UNDEFINED") ; todo
       (define shift-type (decode-shift shift))
       (define shift-amount (bitvector->natural imm6))
       (define invert (equal? N (bv 1 1)))
       (define operand1 (cpu-X cpu datasize rn))
       (define operand2 (shift-reg cpu datasize rm shift-type shift-amount))
       (define op2 (if invert (bvnot operand2) operand2))
       (define result (logical-exec cpu datasize rd op operand1 operand2 setflags))
       (set-cpu-X!  cpu datasize rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_ins_ext_insert_movewide
    [(bvmatch? opcode (bv #b00010010100000000000000000000000 32)
                      (bv #b00011111100000000000000000000000 32))
       (define opc   (extract 30 29 opcode))
       (define hw    (extract 22 21 opcode))
       (define imm16 (extract 20  5 opcode))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define datasize  (* 8 datasize8))
       (define old (if (equal? opc (bv #b11 2)) (cpu-X cpu datasize rd) (bv 0 datasize)))
       ; (printf "move-immediate ~a ~a ~a\n" old imm16 hw)
       (define res0 (cond
           [(equal? hw (bv #b00 2)) (bvinsert 15  0 imm16 old)]
           [(equal? hw (bv #b01 2)) (bvinsert 31 16 imm16 old)]
           [(equal? hw (bv #b10 2)) (bvinsert 47 32 imm16 old)]
           [else                    (bvinsert 63 48 imm16 old)]))
       (define result (if (equal? opc (bv #b00 2)) (bvnot res0) res0))
       (set-cpu-X!  cpu datasize rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_integer_arithmetic_mul_uniform_add_sub
    [(bvmatch? opcode (bv #b00011011000000000000000000000000 32)
                      (bv #b01111111111000000000000000000000 32))
       (define o0     (extract 15 15 opcode))
       (define ra     (bitvector->natural (extract 14 10 opcode)))
       (define sub-op (equal? o0 (bv 1 1)))
       (define datasize8 (if (equal? sf (bv 1 1)) 8 4))
       (define datasize  (* 8 datasize8))
       (define operand1 (cpu-X cpu datasize rn))
       (define operand2 (cpu-X cpu datasize rm))
       (define operand3 (cpu-X cpu datasize ra))
       (define result
         (if sub-op
           (+ operand3 (* operand1 operand2))
           (- operand3 (* operand1 operand2))))
       (set-cpu-X! cpu datasize rd result)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_literal_general
    [(bvmatch? opcode (bv #b00011000000000000000000000000000 32)
                      (bv #b00111111000000000000000000000000 32))
       (define opc       (extract 31 30 opcode))
       (define imm19     (extract 23  5 opcode))

       (define-values (datasize8 signed memop)
         (cond
           [(equal? opc (bv #b00 2)) (values 4      #f 'load)]
           [(equal? opc (bv #b01 2)) (values 8      #f 'load)]
           [(equal? opc (bv #b10 2)) (values 4      #t 'load)]
           [(equal? opc (bv #b11 2)) (values (void) #f 'prefetch)]))
       (define datasize (* 8 datasize8))
       (define offset   (sign-extend (concat imm19 (bv 0 2)) core:i64))
       (define address  (cpu-pc cpu))
       (case memop
         [(load)
                 (define data (mem-read cpu datasize8 address offset))
                 (if signed
                   (set-cpu-X! cpu 64 rd (sign-extend data core:i64))
                   (set-cpu-X! cpu datasize rd data))]
         [(prefetch)
          (core:bug-on #t #:msg "LDR literal prefetch unimplemented")])
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_single_general_immedate_signed_offset_normal
    [(bvmatch? opcode (bv #b00111000000000000000000000000000 32)
                      (bv #b00111111001000000000110000000000 32))
       (define size      (extract 31 30 opcode))
       (define opc       (extract 23 22 opcode))
       (define imm9      (extract 20 12 opcode))
       (define postindex (equal? (extract 11 11 opcode) (bv 0 1)))
       (define scale     (bitvector->natural size))
       (define-values    (memop signed regsize datasize8) (ldst-common size opc scale))
       (define offset    (sign-extend imm9 core:i64))
       (ldst-exec cpu rd rn memop signed datasize8 regsize offset #:wback #f #:postindex #f)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_single_general_immedate_signed_pre/post_idx
    [(bvmatch? opcode (bv #b00111000000000000000010000000000 32)
                      (bv #b00111111001000000000110000000000 32))
       (define size      (extract 31 30 opcode))
       (define opc       (extract 23 22 opcode))
       (define imm9      (extract 20 12 opcode))
       (define postindex (equal? (extract 11 11 opcode) (bv 0 1)))
       (define scale     (bitvector->natural size))
       (define-values    (memop signed regsize datasize8) (ldst-common size opc scale))
       (define offset    (sign-extend imm9 core:i64))
       (ldst-exec cpu rd rn memop signed datasize8 regsize offset #:wback #t #:postindex postindex)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_single_general_immedate_pre/post_idx
    [(bvmatch? opcode (bv #b10111000000000000000010000000000 32)
                      (bv #b10111111001000000000010000000000 32))
       (define size      (extract 31 30 opcode))
       (define opc       (extract 23 22 opcode))
       (define imm9      (extract 20 12 opcode))
       (define postindex (equal? (extract 11 11 opcode) (bv 0 1)))
       (define scale     (bitvector->natural size))
       (define-values    (memop signed regsize datasize8) (ldst-common size opc scale))
       (define offset    (sign-extend imm9 core:i64))
       (ldst-exec cpu rd rn memop signed datasize8 regsize offset #:wback #t #:postindex postindex)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_single_general_immedate_unsigned
    [(bvmatch? opcode (bv #b00111001000000000000000000000000 32)
                      (bv #b00111111001000000000000000000000 32))
       (define size      (extract 31 30 opcode))
       (define opc       (extract 23 22 opcode))
       (define imm12     (extract 21 10 opcode))
       (define scale     (bitvector->natural size))
       (define-values    (memop signed regsize datasize8) (ldst-common size opc scale))
       (define offset    (bvshl (sign-extend imm12 core:i64) (core:bvpointer scale)))
       (ldst-exec cpu rd rn memop signed datasize8 regsize offset #:wback #f #:postindex #f)
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_memory_single_general_register
    [(bvmatch? opcode (bv #b00111000001000000000100000000000 32)
                      (bv #b00111111001000000000110000000000 32))
       (define size        (extract 31 30 opcode))
       (define opc         (extract 23 22 opcode))
       (define option      (extract 15 13 opcode))
       (define S           (extract 12 12 opcode))
       (define scale       (bitvector->natural size))
       (core:bug-on (equal? (extract 1 1 option) (bv 0 1)) #:msg "UNDEFINED") ; todo
       (define extend-type (decode-reg-extend option))
       (define shift       (if (equal? S (bv 1 1)) scale 0))
       (define-values      (memop signed regsize datasize8) (ldst-common size opc scale))
       (define offset      (extend-reg cpu 64 rm extend-type shift))
       (ldst-exec cpu rd rn memop signed datasize8 regsize offset #:wback #f #:postindex #f)
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
       (core:bug-on (equal? V (bv 1 1)) #:msg "SIMD not supported yet 1") ; todo
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
       (core:bug-on (equal? V (bv 1 1)) #:msg "SIMD not supported yet 2") ; todo
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
       (define datasize  (* 8 datasize8))

       (when (equal? rn 31) (check-sp-alignment cpu))
       (define address (cpu-XSP cpu datasize rn))
       (case memop
         [(store)
                  (define data (if pair
                                 (concat (cpu-X cpu datasize rt2) (cpu-X cpu datasize rd))
                                 (cpu-X cpu datasize rd)))
                  (define status
                    (aarch64-exclusive-monitors-pass address datasize8))
                  (when status
                    (mem-write! cpu datasize8 address (bv 0 64) data))
                  (set-cpu-X! cpu datasize rm (if status (bv 0 64) (bv 1 64)))]
         [(load)
                  (aarch64-set-exclusive-monitors address datasize8)
                  (if pair
                    [if (equal? elsize8 4)
                      (begin
                        (define data (mem-read cpu datasize8 address (bv 0 64)))
                        (set-cpu-X! cpu datasize rd  (extract (- (* 8   elsize8) 1)       0 data))
                        (set-cpu-X! cpu datasize rt2 (extract (- (* 8 datasize8) 1) elsize8 data)))
                      (begin
                        ; todo: check 128-bit alignment
                        (define data1 (mem-read cpu datasize8 address (bv 0 64)))
                        (define data2 (mem-read cpu datasize8 address (bv 8 64)))
                        (set-cpu-X! cpu datasize rd  data1)
                        (set-cpu-X! cpu datasize rt2 data2))]
                    [begin
                      (define data (mem-read cpu datasize8 address (bv 0 64)))
                      (set-cpu-X! cpu datasize rd (zero-extend data 64))])])
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
       (define regsize8  (if (equal? elsize8 8) 8 4))
       (define datasize8 elsize8)
       (define regsize   (* 8 regsize8))
       (define datasize  (* 8 datasize8))

       (when (equal? rn 31) (check-sp-alignment cpu))
       (define address (cpu-XSP cpu 64 rn))
       (case memop
         [(store)
                  (define data (cpu-X cpu datasize rd))
                  (mem-write! cpu datasize8 address (bv 0 64) data)]
         [(load)
                  (define data (mem-read cpu datasize8 address (bv 0 64)))
                  (set-cpu-X! cpu regsize rd (zero-extend data regsize))])
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_system_barriers_dmb
    ; aarch64_system_barriers_dsb
    [(bvmatch? opcode (bv #b11010101000000110011000010011111 32)
                      (bv #b11111111111111111111000010011111 32))
     (define CRmh (extract 11 10 opcode))
     (define CRml (extract  9  8 opcode))
     (define opc  (extract  6  5 opcode))
     (core:bug-on (equal? opc (bv 0 2)) #:msg "UNDEFINED") ; todo
     (core:bug-on (equal? opc (bv 3 2)) #:msg "SB") ; todo
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
       (core:bug-on (equal? level (bv 0 2)) #:msg "UNDEFINED") ; todo
       (cond
         [(equal? level (bv 1 2))
           (aarch64-check-for-svc-trap imm16)
           (aarch64-call-supervisor imm16)]
         [(equal? level (bv 2 2))
           (core:bug-on (equal? (cpu-pstate-el cpu) (bv 0 2)) #:msg "UNDEFINED") ; todo: this is missing part of the TrustZone check
           (define hvc-enable #t) ; todo: missing the SCR/HCR check
           (core:bug-on (not hvc-enable) #:msg "UNDEFINED") ; todo
           (aarch64-call-hypervisor imm16)]
         [(equal? level (bv 3 2))
           (aarch64-check-for-smc-undef-or-trap imm16)
           (define smc-enable #t) ; todo: missing the SCR check
           (core:bug-on (not smc-enable) #:msg "UNDEFINED") ; todo
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

    ; aarch64_system_register_system
    [(bvmatch? opcode (bv #b11010101000100000000000000000000 32)
                      (bv #b11111111110100000000000000000000 32))
       (define L           (extract 21 21 opcode))
       (define o0          (extract 19 19 opcode))
       (define op1         (extract 18 16 opcode))
       (define CRn         (extract 15 12 opcode))
       (define CRm         (extract 11  8 opcode))
       (define op2         (extract  5  7 opcode))
       (aarch64-check-system-access (concat (bv 1 1) o0) op1 CRn CRm op2 rd L)
       (define sys_op0 (+ 2 (bitvector->natural o0)))
       (define sys_op1 (bitvector->natural op1))
       (define sys_op2 (bitvector->natural op2))
       (define sys_crn (bitvector->natural CRn))
       (define sys_crm (bitvector->natural CRm))
       (define read (equal? L (bv 1 1)))
       (if read
         (set-cpu-X! cpu 64 (aarch64-sys-reg-read cpu sys_op0 sys_op1 sys_crn sys_crm sys_op2))
         (aarch64-sys-reg-write cpu sys_op0 sys_op1 sys_crn sys_crm sys_op2 (cpu-X cpu 64 rd)))
       (set-cpu-pc! cpu (bvadd pc (bv 4 64)))]

    ; aarch64_system_sysops
    [(bvmatch? opcode (bv #b11010101000010000000000000000000 32)
                      (bv #b11111111110110000000000000000000 32))
     (core:bug-on #t #:msg "todo")] ; the only one I want at the moment is DC

    [else
       (core:bug-on #f #:msg "execute/instr: incomplete pattern match")]
))


; interpret a program from a given cpu state
(define (interpret cpu program)
  ; Use Serval's "split-pc" symbolic optimization
  (core:split-pc (cpu pc) cpu
    (define pc (bitvector->natural (cpu-pc cpu)))
    ; (printf "PC = ~x\n" pc)
    (set-current-pc-debug! pc)
    ; fetch an instruction to execute
    (cond
      [(hash-has-key? program pc)
        (define insn (hash-ref program pc))
        ; (printf "Executing instruction ~x: ~x\n" pc insn)
        (execute cpu (bv insn 32))
        (interpret cpu program)]
      [else ; illegal address - exit
        ; (printf "End of program at ~x\n" pc)
        ; (printf "~a\n" program)
        (void)])))

; end
