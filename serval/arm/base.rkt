#lang rosette

; import serval functions with prefix "core"
(require
  serval/lib/unittest
  rackunit/text-ui
  (prefix-in core:
    (combine-in serval/lib/core
                serval/spec/refinement
                serval/spec/ni))
)

(provide (all-defined-out))

(define current-pc-debug (bv 0 64))

(define (set-current-pc-debug! v)
  (set! current-pc-debug v))

; cpu state: program counter, stack pointer, general purpose registers and flags
; todo: add memory!
(struct cpu
  (pc
   sp
   gprs
   pstate-n
   pstate-z
   pstate-c
   pstate-v
   mregions
   )
   #:mutable #:transparent)

; make copy of cpu state
(define (cpu-copy c)
  (struct-copy cpu c
    [gprs (vector-copy (cpu-gprs c))]
    [mregions (map core:mregion-copy (cpu-mregions c))]))

; concrete cpu state
(define (init-cpu-concrete [symbols null] [globals null])
  (define pc (bv 0 64)) ; todo: make this symbolic, but aligned?
  (define sp (bv #x2000 64)) ; SP is at top of 2nd page of memory
  (define x (make-vector 31 (bv 0 64)))
  (vector-set! x 30 (bv -1 64)) ; set LR to -1 to force program exit (minor hack)
  (define mregions (core:create-mregions symbols globals))
  (cpu pc sp x #f #f #f #f mregions))

; symbolic cpu state
(define (init-cpu-symbolic [symbols null] [globals null])
  (define-symbolic* x64 (bitvector 64) [31])
  (define pc (bv 0 64)) ; todo: make this symbolic, but aligned?
  (define sp (bv #x2000 64)) ; SP is at top of 2nd page of memory
  (define x (apply vector x64))
  (vector-set! x 30 (bv -1 64)) ; set LR to -1 to force program exit (minor hack)
  (define-symbolic n z c v boolean?) ; todo: do I want these to be boolean? or bit?
  (define mregions (core:create-mregions symbols globals))
  ; (for/list ([mr (in-list mregions)]) (printf "MRegion ~a\n" mr))
  (cpu pc sp x n z c v mregions))


; read/write GPR[i]
(define (cpu-gpr c i) (vector-ref (cpu-gprs c) i))
(define (set-cpu-gpr! c i v) (vector-set! (cpu-gprs c) i v))

(define/contract (cpu-X c i)
  (-> cpu? integer? (bitvector 64))
  (if (= i 31) (bv 0 64) (cpu-gpr c i))
)

(define/contract (set-cpu-X! c i x)
  (-> cpu? integer? (bitvector 64) void)
  ; (printf "set-cpu-X! X~a <- ~a\n" (if (= i 31) "ZR" i) x)
  (when (! (= i 31)) (set-cpu-gpr! c i x))
)

(define/contract (cpu-XSP c i)
  (-> cpu? integer? (bitvector 64))
  (if (= i 31) (cpu-sp c) (cpu-gpr c i))
)

(define/contract (set-cpu-XSP! c i x)
  (-> cpu? integer? (bitvector 64) void)
  ; (printf "set-cpu-XSP! X~a <- ~a\n" i x)
  (if (= i 31) (set-cpu-sp! c x) (set-cpu-gpr! c i x))
)

(define (cpu-mem cpu addr size) #f)
(define (set-cpu-mem! cpu addr size x) #f)

; end
