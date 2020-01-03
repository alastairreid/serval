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

(define (insert hi lo x old)
  ; (printf "insert ~a ~a ~a ~a\n" hi lo x old)
  (define w (+ (- hi lo) 1))
  (define mask (arithmetic-shift (- (arithmetic-shift 1 w) 1) lo))
  (define nmask (bitwise-not mask))
  (bitwise-ior (bitwise-and old nmask)
               (bitwise-and (arithmetic-shift x lo) mask)))

; condition codes
(define cond-eq #b0000)
(define cond-ne #b0000)
(define cond-cs #b0010)
(define cond-cc #b0011)
(define cond-mi #b0100)
(define cond-pl #b0101)
(define cond-vs #b0110)
(define cond-vc #b0111)
(define cond-hi #b1000)
(define cond-ls #b1001)
(define cond-ge #b1010)
(define cond-lt #b1011)
(define cond-gt #b1100)
(define cond-le #b1101)
(define cond-al #b1110)
(define cond-nv #b1111)

(define (add-sub-extended sf rd rn rm op S option imm3)
  (insert 31 31 sf
  (insert 30 30 op
  (insert 29 29 S
  (insert 20 16 rm
  (insert 12 10 imm3
  (insert  9  5 rn
  (insert  4  0 rd
  #b00001011001000000000000000000000))))))))

(define (add-sub-immediate sf rd rn imm12 sh S op)
  (insert  4  0 rd
  (insert  9  5 rn
  (insert 21 10 imm12
  (insert 22 22 sh
  (insert 29 29 S
  (insert 30 30 op
  (insert 31 31 sf
  #b10010001000000000000000000000000))))))))

(define (ret rn)
  (insert  9  5 rn
  #b11010110010111110000000000000000))

(define (cmp-immediate sf rn imm12 sh)
  (add-sub-immediate sf 31 rn imm12 sh 1 1))

(define (csel sf rd rn rm ccode op o2)
  (insert  4  0 rd
  (insert  9  5 rn
  (insert 20 16 rm
  (insert 10 10 o2
  (insert 15 12 ccode
  (insert 30 30 op
  (insert 31 31 sf
  #b00011010100000000000000000000000))))))))

(define (csinc sf rd rn ccode)
  ; todo: this is somewhere between Arm's official CINC and the CSINC mnemonics
  (csel sf rd rn rn ccode 0 1))

(define (cset sf rd ccode)
  ; todo: this flips the meaning of ccode relative to Arm mnemonics
  (csinc sf rd 31 ccode))

(define (csinv sf rd rn ccode)
  (csel sf rd rn rn ccode 1 0))

(define (ldr-imm-post rt rn offset size signed)
  (insert 31 30 size
  (insert 23 22 (if signed #b10 #b01) ; todo: 32-bit
  (insert 20 12 offset ; todo: worry about overflow
  (insert 11 10 #b01
  (insert  9  5 rn
  (insert  4  0 rt
  #b10111000000000000000000000000000)))))))

(define (ldr-imm-pre rt rn offset size signed)
  (insert 31 30 size
  (insert 23 22 (if signed #b10 #b01) ; todo: 32-bit
  (insert 20 12 offset ; todo: worry about overflow
  (insert 11 10 #b11
  (insert  9  5 rn
  (insert  4  0 rt
  #b10111000000000000000000000000000)))))))

(define (ldr-imm-uoffset rt rn offset size signed)
  (insert 31 30 size
  (insert 23 22 (if signed #b10 #b01) ; todo: 32-bit
  (insert 21 10 offset ; todo: worry about overflow
  (insert  9  5 rn
  (insert  4  0 rt
  #b10111010000000000000000000000000))))))

(define (str-imm-post rt rn offset size)
  (insert 31 30 size
  (insert 23 22 #b00
  (insert 20 12 offset ; todo: worry about overflow
  (insert 11 10 #b01
  (insert  9  5 rn
  (insert  4  0 rt
  #b10111000000000000000000000000000)))))))

(define (str-imm-pre rt rn offset size)
  (insert 31 30 size
  (insert 23 22 #b00
  (insert 20 12 offset ; todo: worry about overflow
  (insert 11 10 #b11
  (insert  9  5 rn
  (insert  4  0 rt
  #b10111000000000000000000000000000)))))))

(define (str-imm-uoffset rt rn offset size)
  (insert 31 30 size
  (insert 23 22 #b00
  (insert 21 10 offset ; todo: worry about overflow
  (insert  9  5 rn
  (insert  4  0 rt
  #b10111010000000000000000000000000))))))

(define (mov-immediate sf rd imm16 opc hw)
  (insert 31 31 sf
  (insert 30 29 opc
  (insert 22 21 hw
  (insert 20  5 imm16
  (insert  4  0 rd
  #b00010010100000000000000000000000))))))

(define (movn sf rd imm16 hw)
  (mov-immediate sf rd imm16 #b00 hw))

(define (movz sf rd imm16 hw)
  (mov-immediate sf rd imm16 #b10 hw))

(define (movk sf rd imm16 hw)
  (mov-immediate sf rd imm16 #b11 hw))

; turn a sequence of instructions into a hash table of instructions, starting at address base
(define (asm-block base insns)
  (make-hash (for/list ([i (in-naturals base)] [insn (in-vector insns)]) (cons (* 4 i) insn))))

; end
