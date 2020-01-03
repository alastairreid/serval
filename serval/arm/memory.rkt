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

(provide (all-defined-out))

; memory

(define (resolve-mem-path cpu sz base offset)
  ; (-> cpu? (one-of/c 1 2 4 8) bv? bv? mregion?)
  (define mr (core:guess-mregion-from-addr #:dbg current-pc-debug (memspace-mregions (cpu-physmem cpu)) base offset))
  (core:bug-on (equal? mr #f) #:dbg current-pc-debug #:msg (format "Unable to guess mregion for ~a + ~a" base offset))
  mr)

(define (mkpath mr sz addr)
  (define start (core:mregion-start mr))
  (define end   (core:mregion-end   mr))
  (define name  (core:mregion-name  mr))
  (define block (core:mregion-block mr))

  (define size (core:bvpointer sz))
  ; (printf "resolve: ~a+=~a in region ~a ~a..~a = ~a\n" addr size name start end mr)
  (define region-offset (bvsub addr (bv start 64))) ; offset within region

  (core:bug-on (! (core:mregion-inbounds? mr addr size))
                #:dbg current-pc-debug
                #:msg (format "resolve-mem-path: address out of range:\n addr: ~e\n block: ~e" addr name))
  (define path (core:mblock-path block region-offset size #:dbg current-pc-debug))
  (values block path))

(define (mem-read cpu sz_bytes base offset)
  (define addr (bvadd offset base))
  (define mr (resolve-mem-path cpu sz_bytes base offset))
  (if (equal? mr #f)
    (begin
      (assert (equal? sz_bytes 4))
      (hash-ref (memspace-rom (cpu-physmem cpu)) addr))
    (begin
      (define-values (block path) (mkpath mr sz_bytes addr))
      (core:mblock-iload block path))))

(define (mem-write! cpu sz_bytes base offset value)
  (define addr (bvadd offset base))
  (define mr (resolve-mem-path cpu sz_bytes base offset))
  (if (equal? mr #f)
    (begin
      (assert (equal? sz_bytes 4))
      (hash-set! (memspace-rom (cpu-physmem cpu)) addr value))
    (begin
      (define-values (block path) (mkpath mr sz_bytes addr))
      (core:mblock-istore! block value path))))

; memory barriers

(define (data-memory-barrier cpu domain types) #f)
(define (data-synchronization-barrier cpu domain types) #f)

; memory exclusives

(define (aarch64-exclusive-monitors-pass ptr datasize8)
  (core:bug-on #t "todo"))

(define (aarch64-set-exclusive-monitors address datasize8)
  (core:bug-on #t "todo"))

