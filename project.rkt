;; PL Project - Fall 2018
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs

;; CHANGE add the missing ones

(struct var   (string)  #:transparent)   ;; a variable, e.g., (var "foo")
(struct num   (int)     #:transparent)   ;; a constant number, e.g., (num 17)
(struct bool  (bit) #:transparent)   ;; a boolean, e.g., (bool false)

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

(struct func (n args b) #:transparent)

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
    [(eq? str (car (car env))) (cdr (car env))]
        [#t (envlookup (cdr env) str)]
    )
 )

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e)  ;; Variables
         (envlookup env (var-string e))]

       ;;
       ;; Other 
       ;;

       [(func? e)
        (if (and (or (string? (func-n e)) (null? (func-n e))) (string? (func-args e)))
        (closure env e)
        (error "NUMEX function name and parameter name must be string"))]
        
       [(with? e)
        (eval-under-env (with-e2 e) (cons (cons (with-s e)(with-e1 e)) env))]

       [(apply? e)
        (let ([v1 (eval-under-env (apply-funexp e) env)]
               [v2 (eval-under-env (apply-actual e) env)])
          (if (closure? v1)
              (if (null? (func-n (closure-f v1)))
               (eval-under-env (func-b (closure-f v1)) (cons (cons (func-args (closure-f v1)) v2) (closure-env v1)))
               (eval-under-env (func-b (closure-f v1)) (cons (cons (func-n (closure-f v1)) v1) (cons (cons (func-args (closure-f v1)) v2) (closure-env v1)))))
              (error  "NUMUX apply applied to non-closure")
             ))]
       
       ;;
       ;; Pairs 
       ;;

       [(apair? e)
        (let ([v1 (eval-under-env (apair-e1 e) env)]
              [v2 (eval-under-env (apair-e2 e) env)])
              ((apair v1 v2)))]

       [(1st? e)
        (let ([v1 (eval-under-env (1st-e1 e) env)])
          (if (apair? v1)
              (apair-e1 v1)
              (error "NUMUX 1st applied to non-apair")))]

       [(2nd? e)
        (let ([v1 (eval-under-env (2nd-e1 e) env)])
          (if (apair? v1)
              (apair-e2 v1)
              (error "NUMUX 1st applied to non-apair")))]

       ;;
       ;; Conditions 
       ;;


       [(cnd? e)
        (let ([v1 (eval-under-env (cnd-e1 e) env)])
              (if (bool? v1)
                  (if (bool-bit v1)
                      (eval-under-env (cnd-e2))
                      (eval-under-env (cnd-e3))
                      )
                  (error "NUMUX cnd guard applied to non-boolean"))
              )]

       [(iseq? e)
        (let ([v1 (eval-under-env (iseq-e1 e) env)]
              [v2 (eval-under-env (iseq-e2 e) env)])
              (cond
                [(and (num? v1)(num? v2))
                 (eq? (num-int v1) (num-int v2))]
                [(and (bool? v1)(bool? v2))
                 (eq? (bool-bit v1)(bool-bit v2))]
                [#t (error "NUMUX iseq applied to diffrent types or non-number nor boolean")]
         ))]

       [(ifnzero? e)
        (let ([v1 (eval-under-env (ifnzero-e1 e) env)])
              (if (num? v1)
                  (if (eq? (num-int v1 0))
                      (eval-under-env (ifnzero-e3 e) env)
                      (eval-under-env (ifnzero-e2 e) env))
                  (error "NUMUX ifnzero applied to a non-number")
              ))]

       [(ifleq? e)
        (let ([v1 (eval-under-env (ifleq-e1 e) env)]
              [v2 (eval-under-env (ifleq-e2 e) env)])
              (if (and
                   (num? v2)
                   (num? v1))
                  (if (<= (num-int v1)(num-int v2))
                      (eval-under-env (ifleq-e3 e) env)
                      (eval-under-env (ifleq-e4 e) env))
                  (error "NUMUX ifleq applied to a non-number")
              ))]

       [(ismunit? e)
        (let ([v1 (eval-under-env (ismunit-e e) env)])
              (bool (munit? v1))
         )]

        ;;
        ;; Logical Operations
        ;;
        
        [(andalso? e) 
         (let ([v1 (eval-under-env (andalso-e1 e) env)]
               [v2 (eval-under-env (andalso-e2 e) env)])
           (if (and (bool? v1)
                    (bool? v2))
               (bool (if (eq? (bool-bit v1) #f)
                         (#f)
                         (bool-bit v2)))
               (error "NUMUX and-also applied to non-boolean")
           ))]
        [(orelse? e)
         (let ([v1 (eval-under-env (orelse-e1 e) env)]
               [v2 (eval-under-env (orelse-e2 e) env)])
           (if (and (bool? v1)
                    (bool? v2))
               (bool (if (eq? (bool-bit v1) #t)
                         (#t)
                         (bool-bit v2)))
               (error "NUMUX or-else applied to non-boolean")
           ))]

        ;;
        ;; Arithmetic Operations
        ;;

        [(plus? e) 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to non-number")))]
        [(minus? e) 
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1) 
                       (num-int v2)))
               (error "NUMEX subtraction applied to non-number")))]
        [(mult? e) 
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1) 
                       (num-int v2)))
               (error "NUMEX multiply applied to non-number")))]
        [(div? e) 
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (if (eq? v2 0)
                   (error "NUMEX division applied to Zero")
                   (num (/ (num-int v1) 
                       (num-int v2))))
               (error "NUMEX division applied to non-number")))]
        [(neg? e) 
         (let ([v1 (eval-under-env (neg-e1 e) env)])
           (if (num? v1)
               (num (- (num-int v1)))
               (if (bool? v1)
                   (bool (if v1 #f #t))
                   (error "NUMEX Nagation applied to non-number or non-boolean"))
               ))]
        [(num? e)
         (num (eval-under-env (num-int e) env))]
        [(bool? e)
         (bool (eval-under-env (bool-bit e) env))]
        [(closure? e) e] ;; TODO FIX
        [(number? e)  e]
        [(boolean? e) e]
        [(munit? e) e]
        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))
        
;; Problem 3

(define (ifmunit e1 e2 e3)
  (cnd (ismunit e1) e2 e3)
  )

(define (with* bs e2)
  (if (null? bs)
      e2
      (with (car (car bs)) (cdr (car bs)) (with* (cdr bs) e2))))

(define (ifneq e1 e2 e3 e4)
  (with* (cons (cons "_x" e1) (cons (cons "_y" e2) null))
           (ifleq (var "_x") (var "_y") (ifleq (var "_y") (var "_x") e4 e3) e3))
  )


;; Problem 4

(define (islist l) (cond [(and (apair? l) (islist (2nd l))) #t]
                         [(ismunit l) #t]
                         [#t #f]))

(define (map f l) (cond [(and (func? f)(islist l))
                         (apair (apply f (1st l))(map f (2nd l)))
                         ]
                        [#t (error "type of argument of map function is not right")]))

(define (numex-filter f) (cond [(func? f)
                                (func null "xs" 
                                      (if (islist "xs")
                                           (map f "xs")
                                           (error "NUMEX filter applied to non-list"))
                                       )]
                               [#t (error "numex-filter applied to non NUMEX function types")]
                          ))

;;(define numex-filter (func "_map" "_func" (
;;                                      func "_map_" _list (if (islist _list)
;;                                                            (apair (apply _func (1st _list)) (_map_ (2nd _list)))
;;                                                           (error "NUMEX filter applied to non-list")
;;                                                            )))) 

;;(define numex-all-gt
;;  (with "filter" numex-filter
;;        "CHANGE (notice filter is now in NUMEX scope)"))

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
