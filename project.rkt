;; PL Project - Fall 2018
;; NUMEX interpreter
;; Mohammad Mahdi Rahimi (https://github.com/mahi97)
;; Email: Mohammadmahdi76@gmail.com

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs

;; CHANGE add the missing ones

(struct var   (string)  #:transparent)   ;; a variable, e.g., (var "foo")
(struct num   (int)     #:transparent)   ;; a constant number, e.g., (num 17)
(struct bool  (bit) #:transparent)       ;; a boolean, e.g., (bool false)

(struct plus  (e1 e2)   #:transparent)   ;; add two expressions
(struct minus (e1 e2)   #:transparent)   ;; minus two expressions
(struct mult  (e1 e2)   #:transparent)   ;; multiple two expressions
(struct div   (e1 e2)   #:transparent)   ;; divide two expressions
(struct neg   (e1)      #:transparent)   ;; negation of an expression

(struct andalso (e1 e2) #:transparent)   ;; logical conjunction
(struct orelse  (e1 e2) #:transparent)   ;; logical disjunction

(struct cnd  (e1 e2 e3) #:transparent)   ;; conditions
(struct iseq  (e1 e2)   #:transparent)   ;; add two expressions
(struct ifnzero  (e1 e2 e3)   #:transparent)   ;; add two expressions
(struct ifleq  (e1 e2 e3 e4)   #:transparent)   ;; add two expressions

(struct with  (s e1 e2)   #:transparent)   ;; add two expressions
(struct apair  (e1 e2)   #:transparent)   ;; add two expressions
(struct 1st  (e1)   #:transparent)   ;; add two expressions
(struct 2nd  (e1)   #:transparent)   ;; add two expressions

(struct lam  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct apply (funexp actual)       #:transparent) ;; function application

(struct munit   ()      #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e)     #:transparent) ;; if e1 is unit then true else false

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env f) #:transparent) 

;; Problem 1

(define (racketlist->numexlist xs) (cond [(eq? xs null) (munit)]
                                         [(number? xs) (num xs)]
                                         [(string? xs) (var xs)]
                                         [(boolean? xs) (bool xs)]
                                         [#t (apair (racketlist->numexlist (car xs))
                                                   (racketlist->numexlist (cdr xs)))]
                                         ))
(define (numexlist->racketlist xs) (cond [(munit? xs) null]
                                         [(num? xs) (num-int xs)]
                                         [(var? xs) (var-string xs)]
                                         [(bool? xs) (bool-bit xs)]
                                         [#t (cons (numexlist->racketlist (apair-e1 xs))
                                                   (numexlist->racketlist (apair-e2 xs))
                                                   )]
                                    ))

;; Problem 2

;; lookup a variable in an environment
;; Complete this function
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
  		"CHANGE" 
		)
 )

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]
        [(plus? e) 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to non-number")))]
        ;; CHANGE add more cases here
        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))
        
;; Problem 3

(define (ifmunit e1 e2 e3) "CHANGE")

(define (with* bs e2) "CHANGE")

(define (ifneq e1 e2 e3 e4) "CHANGE")

;; Problem 4

(define numex-filter "CHANGE")

(define numex-all-gt
  (with "filter" numex-filter
        "CHANGE (notice filter is now in NUMEX scope)"))

;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e) "CHANGE")

;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env) "CHANGE")

;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))
