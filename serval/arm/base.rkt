#lang rosette

; import serval functions with prefix "core"
(require
  serval/lib/unittest
  rackunit/text-ui
  (prefix-in core:
    (combine-in serval/lib/core
                serval/spec/refinement
                serval/spec/ni))
  (prefix-in rosette:
    rosette/base/core/bitvector)
)

(provide (all-defined-out))

#| Library functions |#

; set old[hi:lo] to x
(define (bvinsert hi lo x old)
  (define max (- (core:bv-size old) 1))
  ; (printf "bvinsert ~a ~a ~a ~a ~a\n" max hi lo x old)
  (core:bug-on (< max hi) #:msg "bvinsert: hi out of range")
  (core:bug-on (< hi lo)  #:msg "bvinsert: lo out of range")
  (core:bug-on (not (= (+ (- hi lo) 1) (core:bv-size x))) #:msg "bvinsert: inserted value wrong size")
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

#| Machine state |#

(define current-pc-debug (bv 0 64))

(define (set-current-pc-debug! v)
  (set! current-pc-debug v))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; physical memory space
;
; this is a wrapper around Serval's mregion abstraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct memspace
  (mregions
   rom)
  #:mutable #:transparent)

(define (create-memspace symbols globals rom)
  (define mrs (core:create-mregions symbols globals))
  (memspace mrs rom))

(define (memspace-copy m)
  (struct-copy memspace m
    [mregions (map core:mregion-copy (memspace-mregions m))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; cpu state: program counter, stack pointer, general purpose registers and flags
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct cpu
  (pc
   sp
   gprs
   pstate-n
   pstate-z
   pstate-c
   pstate-v
   pstate-el
   physmem
   )
   #:mutable #:transparent)

; make copy of cpu state
(define (cpu-copy c)
  (struct-copy cpu c
    [gprs (vector-copy (cpu-gprs c))]
    [physmem (memspace-copy (cpu-physmem c))]))

; concrete cpu state
(define (init-cpu-concrete [symbols null] [globals null] [rom null])
  (define pc (bv 0 64)) ; todo: make this symbolic, but aligned?
  (define sp (bv #x2000 64)) ; SP is at top of 2nd page of memory
  (define x (make-vector 31 (bv 0 64)))
  (vector-set! x 30 (bv -1 64)) ; set LR to -1 to force program exit (minor hack)
  (define physmem (create-memspace symbols globals rom))
  (cpu pc sp x #f #f #f #f (bv 3 2) physmem))

; symbolic cpu state
(define (init-cpu-symbolic [symbols null] [globals null] [rom null])
  (define-symbolic* x64 (bitvector 64) [31])
  (define pc (bv 0 64)) ; todo: make this symbolic, but aligned?
  (define sp (bv #x2000 64)) ; SP is at top of 2nd page of memory
  (define x (apply vector x64))
  (vector-set! x 30 (bv -1 64)) ; set LR to -1 to force program exit (minor hack)
  (define-symbolic n z c v boolean?) ; todo: do I want these to be boolean? or bit?
  (define physmem (create-memspace symbols globals rom))
  (cpu pc sp x n z c v (bv 3 2) physmem))


; read/write GPR[i]
(define (cpu-gpr c i) (vector-ref (cpu-gprs c) i))
(define (set-cpu-gpr! c i v) (vector-set! (cpu-gprs c) i v))

(define/contract (cpu-X c N i)
  (-> cpu? integer? integer? bv?)
  (if (= i 31) (bv 0 N) (extract (- N 1) 0 (cpu-gpr c i)))
)

(define/contract (set-cpu-X! c N i x)
  (-> cpu? integer? integer? bv? void)
  ; (printf "set-cpu-X! ~a X~a <- ~a\n" N (if (= i 31) "ZR" i) x)
  (when (! (= i 31)) (set-cpu-gpr! c i (zero-extend x (bitvector N))))
)

(define/contract (cpu-XSP c N i)
  (-> cpu? integer? integer? bv?)
  (extract (- N 1) 0 (if (= i 31) (cpu-sp c) (cpu-gpr c i)))
  )

(define/contract (set-cpu-XSP! c N i x)
  (-> cpu? integer? integer? bv? void)
  ; (printf "set-cpu-XSP! X~a <- ~a\n" i x)
  (define x1 (zero-extend x (bitvector 64)))
  (if (= i 31) (set-cpu-sp! c x1) (set-cpu-gpr! c i x1))
)

; end
