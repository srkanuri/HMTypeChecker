#lang racket

(define env '((+ . (-> Int Int Int))
              (- . (-> Int Int Int))
              (* . (-> Int Int Int))
              (/ . (-> Int Int Int))
              (add1 . (-> Int Int))
              (sub1 . (-> Int Int))))

(define (infer-type env e)
  (match e
    [(? number?) 'Int]
    [(? boolean?) 'Bool]
    []))

(define (unify t1 t2)
  (match `(e1 e2)
    [`((,op ,e1 ,e2) (,op ,e1^ ,e2^)) (and (unify e1 e1^) (unify e2 e2^))]
    [`((,op ,e1) (,op ,e1^)) (unify e1 e1^)]
    [`(Int Int) #t]
    [else "Cant Unify expressions"]))

(define (mgu t1 t2)
  (cond
    ((and (pair? t1) (pair? t2))  (match-let* (((list _ t1l t1r) t1)
                                               ((list _ t2l t2r) t2)
                                               (s1 (mgu t1l t2l))
                                               (s2 (mgu (substitute s1 t1r)
                                                        (substitute s1 t2r))))
                                    (set-union s1 s2)))
    ((eq? t1 t2) (set))
    ((number? t1) (varbind t1 t2))
    ((number? t2) (varbind t2 t1))
    (else 'error)))

(define (bottom_up exp monos)
  (if (pair? exp)
      (case (car exp)
        [(lambda) (bottom_up_abs exp monos)]
        [(let)    (bottom_up_let exp monos)]
        [else     (bottom_up_app exp monos)])
      (if (symbol? exp)
          (bottom_up_var exp)
          (bottom_up_lit exp))))

; [Var]
(define (bottom_up_var x)
  (let ((beta (create_fresh_type_variable)))
    (list (mutable-set (cons x beta)) (mutable-set) beta)))

; [App]
(define (bottom_up_app exp monos)
  (let ((e1 (car exp))
        (e2 (cadr exp))
        (beta (create_fresh_type_variable)))
    (match-define (list a1 c1 t1) (bottom_up e1 monos))
    (match-define (list a2 c2 t2) (bottom_up e2 monos))
    (set-union! a1 a2)
    (set-union! c1 c2 (set (list 'equal t1 (list '-> t2 beta))))
    (list a1 c1 beta)))

; [Abs]
(define (bottom_up_abs exp monos)
  (let ((x (caadr exp))
        (e (caddr exp))
        (beta (create_fresh_type_variable))
        (c (mutable-set))
        (a2 (mutable-set)))
    (match-define (list a c t) (bottom_up e (set-add monos x)))
    (set-for-each a (lambda (y)
                      (if (eq? (car y) x)
                          (set-add! c (list 'equal (cdr y) beta))
                          (set-add! a2 y))))
    (list a2 c (list '-> beta t))))

; [Let]
(define (bottom_up_let exp monos)
  (let ((x (car (caadr exp)))
        (e1 (cadr (caadr exp)))
        (e2 (caddr exp)))
    (match-define (list a1 c1 t1) (bottom_up e1 monos))
    (match-define (list a2 c2 t2) (bottom_up e2 monos))
    (set-union! c1 c2)
    (set-for-each a2 (lambda (a)
                       (if (eq? (car a) x)
                           (set-add! c1 (list 'implicit (cdr a) t1 monos))
                           (set-add! a1 a))))
    (list a1 c1 t2)))


; [Lit]
(define (bottom_up_lit exp)
  (list (mutable-set)
        (mutable-set)
        (cond ((number?  exp) 'int)
              ((string?  exp) 'string)
              ((boolean? exp) 'boolean)
              (else 'unknown))))


