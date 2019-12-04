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
    ; add-sub-extended
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

    ; add-sub-immediate
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

    ; branch-conditional
    [(bvmatch? opcode (bv #b01010100000000000000000000000000 32)
                      (bv #b11111111100000000000000000010000 32))
       (define imm19  (extract 23 05 opcode))
       (define ccode  (extract  3  0 opcode))
       (define offset (sign-extend (concat imm19 (bv 0 2)) 64))
       (if (condition-holds cpu ccode)
         (set-cpu-pc! cpu (bvadd pc offset))
         (set-cpu-pc! cpu (bvadd pc (bv 4 64))))]

    ; branch-indirect
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

    ; branch-unconditional
    [(bvmatch? opcode (bv #b00010100000000000000000000000000 32)
                      (bv #b01111100000000000000000000000000 32))
       (define op     (extract 31 31 opcode))
       (define imm25  (extract 25  0 opcode))
       (define target (bvadd pc imm25))

       (when (equal? op (bv #b1 1)) (set-cpu-X! cpu 30 (bvadd pc (bv 4 64)))) ; BL
       (set-cpu-pc! cpu target)]

    ; condsel
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

    ; load-store-register-immediate-pre/postindex
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

    ; load-store-register-immediate-unsigned-offset
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

    ; load-store-register
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

    ; move-immediate
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
