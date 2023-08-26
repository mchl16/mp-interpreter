#lang plait

#| type definitions |#

(define-type Exp
  (numE [n : Number])
  (opE [op : Symbol] [e1 : Exp] [e2 : Exp])
  (ifE [e : Exp] [et : Exp] [ef : Exp])
  (varE [v : Symbol])
  (letE [x : Symbol] [e1 : Exp] [e2 : Exp]) 
  (defE [x : (Listof Symbol)] [e1 : (Listof Exp)] [e2 : Exp])
  (funE [args : (Listof Symbol)] [e : Exp])
  (appE [f : Exp] [args : (Listof Exp)]))



(define-type-alias Value Number)



(define-type ProtoValue ;a wrapper for both values and functions (to store them in an environment)
  (numV [n : Value])
  (funV [args : (Listof Symbol)] [e : Exp] [env : Env]))



(define-type Storable ;a wrapper for the above (or an undefined value), this is what the environment actually stores
  (undefS)
  (valS (v : ProtoValue)))



(define-type Binding ;binds symbols to protovalues
  (bind [name : Symbol]
        [val : (Boxof Storable)]))

(define-type-alias Env (Listof Binding)) ;self-explanatory

#| end of type definitions |#

#| parser |#

(define (check-unique (l : (Listof Symbol))) : Boolean   ;two utility functions for the parser
  (cond
    [[empty? l] #t]
    [[member (first l) (rest l)] #f]
    [else [check-unique (rest l)]]))



(define (check-primop [s : Symbol]) : Boolean
  (cond
    [[equal? s '+] #t]
    [[equal? s '-] #t]
    [[equal? s '*] #t]
    [[equal? s '<=] #t]
    [else #f]))



(define (parse [s : S-Exp]) : Exp                         ;the first parsing stage 
  (let ([S (if (s-exp-list? s) (s-exp->list s) (list s))])
    (cond
      [[s-exp-match? `{define {ANY ...} for ANY} s]
       [let* ([L (if (s-exp-list? (second S)) (s-exp->list (second S))
                     (error 'parse "Parsing error: the program doesn't contain a valid list of function definitions"))]
              [F [defE
                   (map (lambda (x)
                          (s-exp->symbol
                           (if (s-exp-list? x)
                               (let ([l (s-exp->list x)])
                                 (cond
                                   [[empty? l]
                                    [error 'parse "Parsing error: at least one of function definitions is malformed"]]
                                   [[empty? (rest l)]
                                    [error 'parse "Parsing error: at least one of function definitions is malformed"]]
                                   [else [second l]]))
                               (error 'parse "Parsing error: the program doesn't contain a valid list of function definitions"))))
                        L)
                 (map (lambda (x) (parse-function x)) L)
                 (parse-exp (list-ref S 3))]])
         (if (check-unique (defE-x F))
             F
             (error 'parse "Parsing error: defined functions must have unique names"))]]
      [else [error 'parse "Parsing error: the program doesn't follow the \"define (<function definitions>) for <expression>\" format"]])))



(define (parse-function [s : S-Exp]) : Exp    ;parse function definitions
  (let ([S (if (s-exp-list? s) (s-exp->list s) (list s))])
    (cond
    [[s-exp-match? `{fun SYMBOL {SYMBOL ...} = ANY} s]
       [let ([F (funE (map (lambda (x) (s-exp->symbol x)) (s-exp->list (list-ref S 2))) (parse-exp (list-ref S 4)))])
         (if (check-unique (funE-args F))
             F
             (error 'parse "Parsing error: function parameters must have unique names"))]]
    [else [error 'parse "Parsing error: at least one of function definitions is malformed"]])))



(define (parse-exp [s : S-Exp]) : Exp                          ;parse expressions
  (let ([S (if (s-exp-list? s) (s-exp->list s) (list s))])
    (cond
      [[s-exp-match? `NUMBER s]
       [numE (s-exp->number s)]]
      
      [[s-exp-match? `{let SYMBOL be ANY in ANY} s]
       [letE (s-exp->symbol (list-ref S 1)) (parse-exp (list-ref S 3)) (parse-exp (list-ref S 5))]]
      
      [[s-exp-match? `{ifz ANY then ANY else ANY} s]
       [ifE (parse-exp (list-ref S 1)) (parse-exp (list-ref S 3)) (parse-exp (list-ref S 5))]]
      
      [[s-exp-match? `SYMBOL s]
       [varE (s-exp->symbol s)]]
      
      [[s-exp-match? `{SYMBOL {ANY ...}} s]
       [appE (parse-exp (first S)) (map (lambda (x) (parse-exp x)) (s-exp->list (second S)))]]
      
      [[s-exp-match? `{ANY SYMBOL ANY} s]
       [let ([op (s-exp->symbol (second S))])
         (if (check-primop op)
             (opE op (parse-exp (first S)) (parse-exp (third S)))
             (error 'parse "Parsing error: unrecognized primitive operation"))]]
      
      [else [error 'parse "Parsing error: at least one of subexpressions doesn't follow the syntax rules"]])))

#| end of parser |#

#| evaluation functions |#

(define (extend-env-undef [env : Env] [x : (Listof Symbol)]) : Env
  (if (empty? x)
      env
      (cons (bind (first x) (box (undefS))) (extend-env-undef env (rest x)))))



(define (find-var [env : Env] [x : Symbol]) : (Boxof Storable) ;find a symbol in an environment and return what's bound to it
  (type-case (Listof Binding) env
    [empty
     [error 'eval (string-append "Evaluation error: referenced an unscoped symbol: " (symbol->string x))]]
    [[cons b rst-env]
     [cond
       [[eq? x (bind-name b)]
        [bind-val b]]
       [else
        [find-var rst-env x]]]]))



(define (lookup-env [x : Symbol] [env : Env]) : ProtoValue ;get a protovalue bound to a symbol
  (type-case Storable (unbox (find-var env x))
    [[valS v]
     v]
    [[undefS]
     [error 'eval (string-append "Evaluation error: referenced a symbol without a bound value: " (symbol->string x))]]))



(define (update-env! [env : Env] [x : (Listof Symbol)] [v : (Listof ProtoValue)]) : Void ;update environment with new bindings
  (cond
    [[or (and (empty? x) (cons? v)) (and (empty? v) (cons? x))] ;sadly xor doesn't exist in Plait and has to be defined manually
     [error 'eval "Evaluation error: provided an incorrect number of arguments for a function (either in a definition or in a call)"]]
    
    [[empty? x] ;all variables have been updated
     [void]]
    
    [else
     [begin
       (set-box! (find-var env (first x)) (valS (first v)))
       (update-env! env (rest x) (rest v))]]))



(define (extend-env-def [env : Env] [x : (Listof Symbol)] [v : (Listof ProtoValue)]) : Env ;a combo of extend-env-undef and update-env!
  (let ([new-env (extend-env-undef env x)])
    (begin
      (update-env! new-env x v)
      new-env)))



(define (apply [v1 : ProtoValue] [v2 : (Listof ProtoValue)]) : Value
  (type-case ProtoValue v1
    [[funV x b env]
     [eval b (extend-env-def env x v2)
           "Evaluation error: functions cannot evaluate to a non-number"]]
    [else (error 'eval "Evaluation error: attempted to use a non-function as a function")])) ;this line shouldn't be reached, but I'll keep it for safety reasons



(define (parse-op [op : Symbol]) : (Value Value -> Value)
  (cond
    [[equal? op '+] +]
    [[equal? op '-] -]
    [[equal? op '*] *]
    [[equal? op '<=] [lambda (x y) (if (<= x y) 0 2137)]]
    [else [error 'eval "Evaluation error: unrecognized primitive operation"]])) ;this line shouldn't be reached, but I'll keep it for safety reasons



(define (eval-function [e : Exp] [env : Env] [error-message : String]) : ProtoValue ;used to evaluate functions
    (type-case Exp e
      [[funE args e] [funV args e env]]
      [[varE v] [type-case ProtoValue (lookup-env v env)
                [[funV args e env] [funV args e env]]
                [else [error 'eval "Evaluation error: attempted to use a non-function as a function"]]]]
      [else [error 'eval error-message]]))



(define (eval [e : Exp] [env : Env] [error-message : String]) : Value ;evaluates everything but functions
  (type-case Exp e
    [[numE n] n]
    
    [[ifE a b c]
     [eval (if
            (= 0 (eval a env "Evaluation error: attempted to use a non-number as a condition in a conditional statement"))
            b
            c) env "Evaluation error: attempted to evaluate a conditional statement to a non-number"]]

    [[opE op a b] [(parse-op op)
                   (eval a env "Evaluation error: attempted to apply a primitive operation to a non-number")
                   (eval b env "Evaluation error: attempted to apply a primitive operation to a non-number")]]
    
    [[appE e1 e2]
     [apply (eval-function e1 env "Evaluation error: attempted to use a non-function as a function")
            (map (lambda (x)
                   (numV (eval x env
                               "Evaluation error: attempted to use a non-number as a function parameter"))) e2)]] ;this needs to be cast to a protovalue to use in an enviroment
    
    [[varE v] [type-case ProtoValue (lookup-env v env)
                [[numV n] n]
                [else [error 'eval error-message]]]] 

    [[letE x e1 e2]
     [eval e2
           (extend-env-def env
                           (list x)
                           (list (numV (eval e1 env "Evaluation error: attempted to use a non-number as a substituted value in a \"let\" statement")))) ;yet again
           "Evaluation error: attempted to evaluate a \"let\" statement to a non-number"]]
    
    [[defE x e1 e2]
     [let* ([new-env (extend-env-undef '() x)]
            [v1 (map (lambda (x)
                       (eval-function x new-env "Evaluation error: attempted to define a non-function as a function in a definition"))
                     e1)])
       (begin (update-env! new-env x v1) ;this can't be done with extend-env-def as we need to calculate the new values in an extended environment
              (eval e2 new-env error-message))]]

    [[funE x b]
     [error 'eval error-message]])) ;this line shouldn't be reached, but this case still has to be considered in a type-case statement

#| end of evaluation functions |#

#| runner |#

(define (run [s : S-Exp]) : Value
  (eval (parse s) '() "Evaluation error: a program cannot evaluate to a non-number"))

#| end of runner |#