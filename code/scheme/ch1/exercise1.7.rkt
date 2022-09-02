#lang eopl
; (define nth-element
;   (lambda (lst n)
;     (nth-element-help lst n lst n)))

; (define nth-element-help
;   (lambda (lst n lst-origin n-origin)
;     (if (null? lst)
;         (report-list-too-short lst-origin n-origin)
;         (if (zero? n)
;             (car lst)
;             (nth-element-help (cdr lst) (- n 1) lst-origin n-origin)))))

; (define report-list-too-short
;   (lambda (lst n)
;     (eopl:error 'nth-element
;                 "~s does not have ~s elements.~%" lst (+ n 1))))

; (nth-element '(0 1 2 3) 4)