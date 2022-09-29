#lang eopl
(require rackunit)

; Env = (empty-env) | (extend-env Var SchemeVal Env)
; Var = Sym

(define env-tree
  (lambda (var val left right)
    (list var val left right)))

(define env-tree-empty
  (lambda () '()))

(define env-var
  (lambda (env-tree)
    (car env-tree)))

(define env-val
  (lambda (env-tree)
    (cadr env-tree)))

(define env-left
  (lambda (env-tree)
    (caddr env-tree)))

(define env-right
  (lambda (env-tree)
    (cadddr env-tree)))

(define symbol<?
  (lambda (s1 s2)
    (string<? (symbol->string s1) (symbol->string s2))))

(define symbol=?
  (lambda (s1 s2)
    (eqv? s1 s2)))

(define empty-env env-tree-empty)

(define extend-env
  (lambda (var val env)
    (cond
      [(equal? env (empty-env)) (env-tree var val '() '())]
      [(symbol=? var (env-var env)) (env-tree var val env '())]
      [(symbol<? var (env-var env)) (env-tree (env-var env) (env-val env) (extend-env var val (env-left env)) (env-right env))]
      [else (env-tree (env-var env) (env-val env) (env-left env) (extend-env var val (env-right env)))])))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define apply-env
  (lambda (env search-var)
    (cond
      [(equal? env (empty-env)) (report-no-binding-found search-var)]
      [(eqv? (env-var env) search-var) (env-val env)]
      [(symbol<? search-var (env-var env)) (apply-env (env-left env) search-var)]
      [else (apply-env (env-right env) search-var)])))

;;; test

(define env
  (extend-env 'd 6
              (extend-env 'y 8
                          (extend-env 'x 7
                                      (extend-env 'y 14
                                                  (empty-env))))))

(check-equal? (apply-env env 'd) 6)
(check-equal? (apply-env env 'y) 8)
(check-equal? (apply-env env 'x) 7)

(apply-env env 'z)