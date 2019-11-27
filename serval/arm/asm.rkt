#lang rosette

; import serval functions with prefix "core:"
(require
  serval/lib/unittest
  rackunit/text-ui
  (prefix-in core:
    (combine-in serval/lib/core
                serval/spec/refinement
                serval/spec/ni))

  ; import Arm AArch64
  "base.rkt" "interp.rkt"
)

(provide (all-defined-out) (all-from-out "base.rkt"))

#|
  Poor man's assembler
|#

; condition codes
(define cond-eq (bv #b0000 4))
(define cond-ne (bv #b0000 4))
(define cond-cs (bv #b0010 4))
(define cond-cc (bv #b0011 4))
(define cond-mi (bv #b0100 4))
(define cond-pl (bv #b0101 4))
(define cond-vs (bv #b0110 4))
(define cond-vc (bv #b0111 4))
(define cond-hi (bv #b1000 4))
(define cond-ls (bv #b1001 4))
(define cond-ge (bv #b1010 4))
(define cond-lt (bv #b1011 4))
(define cond-gt (bv #b1100 4))
(define cond-le (bv #b1101 4))
(define cond-al (bv #b1110 4))
(define cond-nv (bv #b1111 4))

(define (add-sub-extended rd rn rm op S option imm3)
  (bvinsert 30 30 op
  (bvinsert 29 29 S
  (bvinsert 20 16 (bv rm 5)
  (bvinsert 12 10 imm3
  (bvinsert  9  5 (bv rn 5)
  (bvinsert  4  0 (bv rd 5)
  (bv #b00001011001000000000000000000000 32))))))))

(define (add-sub-immediate rd rn imm12 sh S op)
  (bvinsert  4  0 (bv rd 5)
  (bvinsert  9  5 (bv rn 5)
  (bvinsert 21 10 imm12
  (bvinsert 22 22 sh
  (bvinsert 29 29 S
  (bvinsert 30 30 op
  (bv #b10010001000000000000000000000000 32))))))))

(define (ret rn)
  (bvinsert  9  5 (bv rn 5)
  (bv #b11010110010111110000000000000000 32)))

(define (cmp-immediate rn imm12 sh)
  (add-sub-immediate 31 rn imm12 sh (bv 1 1) (bv 1 1)))

(define (csel rd rn rm ccode op o2)
  (bvinsert  4  0 (bv rd 5)
  (bvinsert  9  5 (bv rn 5)
  (bvinsert 20 16 (bv rm 5)
  (bvinsert 10 10 o2
  (bvinsert 15 12 ccode
  (bvinsert 30 30 op
  (bv #b00011010100000000000000000000000 32))))))))

(define (csinc rd rn ccode)
  ; todo: this is somewhere between Arm's official CINC and the CSINC mnemonics
  (csel rd rn rn ccode (bv 0 1) (bv 1 1)))

(define (cset rd ccode)
  ; todo: this flips the meaning of ccode relative to Arm mnemonics
  (csinc rd 31 ccode))

(define (csinv rd rn ccode)
  (csel rd rn rn ccode (bv 1 1) (bv 0 1)))

(define (ldr-imm-post rt rn offset size signed)
  (bvinsert 31 30 size
  (bvinsert 23 22 (if signed (bv #b10 2) (bv #b01 2)) ; todo: 32-bit
  (bvinsert 20 12 (bv offset 9) ; todo: worry about overflow
  (bvinsert 11 10 (bv #b01 2)
  (bvinsert  9  5 (bv rn 5)
  (bvinsert  4  0 (bv rt 5)
  (bv #b10111000000000000000000000000000 32))))))))

(define (ldr-imm-pre rt rn offset size signed)
  (bvinsert 31 30 size
  (bvinsert 23 22 (if signed (bv #b10 2) (bv #b01 2)) ; todo: 32-bit
  (bvinsert 20 12 (bv offset 9) ; todo: worry about overflow
  (bvinsert 11 10 (bv #b11 2)
  (bvinsert  9  5 (bv rn 5)
  (bvinsert  4  0 (bv rt 5)
  (bv #b10111000000000000000000000000000 32))))))))

(define (ldr-imm-uoffset rt rn offset size signed)
  (bvinsert 31 30 size
  (bvinsert 23 22 (if signed (bv #b10 2) (bv #b01 2)) ; todo: 32-bit
  (bvinsert 21 10 (bv offset 12) ; todo: worry about overflow
  (bvinsert  9  5 (bv rn 5)
  (bvinsert  4  0 (bv rt 5)
  (bv #b10111010000000000000000000000000 32)))))))

(define (str-imm-post rt rn offset size)
  (bvinsert 31 30 size
  (bvinsert 23 22 (bv #b00 2)
  (bvinsert 20 12 (bv offset 9) ; todo: worry about overflow
  (bvinsert 11 10 (bv #b01 2)
  (bvinsert  9  5 (bv rn 5)
  (bvinsert  4  0 (bv rt 5)
  (bv #b10111000000000000000000000000000 32))))))))

(define (str-imm-pre rt rn offset size)
  (bvinsert 31 30 size
  (bvinsert 23 22 (bv #b00 2)
  (bvinsert 20 12 (bv offset 9) ; todo: worry about overflow
  (bvinsert 11 10 (bv #b11 2)
  (bvinsert  9  5 (bv rn 5)
  (bvinsert  4  0 (bv rt 5)
  (bv #b10111000000000000000000000000000 32))))))))

(define (str-imm-uoffset rt rn offset size)
  (bvinsert 31 30 size
  (bvinsert 23 22 (bv #b00 2)
  (bvinsert 21 10 (bv offset 12) ; todo: worry about overflow
  (bvinsert  9  5 (bv rn 5)
  (bvinsert  4  0 (bv rt 5)
  (bv #b10111010000000000000000000000000 32)))))))

(define (mov-immediate rd imm16 opc hw)
  (bvinsert 30 29 opc
  (bvinsert 22 21 hw
  (bvinsert 20  5 imm16
  (bvinsert  4  0 (bv rd 5)
  (bv #b00010010100000000000000000000000 32))))))

(define (movn rd imm16 hw)
  (mov-immediate rd imm16 (bv #b00 2) (bv hw 2)))

(define (movz rd imm16 hw)
  (mov-immediate rd imm16 (bv #b10 2) (bv hw 2)))

(define (movk rd imm16 hw)
  (mov-immediate rd imm16 (bv #b11 2) (bv hw 2)))

; turn a sequence of instructions into a hash table of instructions, starting at address base
(define (asm-block base insns)
  (make-hash (for/list ([i (in-naturals base)] [insn (in-vector insns)]) (cons (bv (* 4 i) 64) insn))))

; end
