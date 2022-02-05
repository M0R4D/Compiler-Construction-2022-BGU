;; ------ constants test ------
{
    1
    3.5
    1e2
    "a"
    'b
    "hello world!"
    '(a b c)
    '(a () (+ 3 4) 9)
    ;;#(3 4 5)
}

;; ------ If test ------
{
    (if #t 1 2)
    (if #f 1 2)
    (if 1 'pass 'fail)
    (if '() 'pass 'fail)
    (if 'a 'excellent 'no-no)
    (if #f 'this-should-not-happen 'correct)
    #;(if 'a 'b 'c)
}

;; ------ And test ------
{
    (and)
    (and #t)
    (and #f)
    (and 1 2 3 #f)
    (and 1 2 #t 3 '() "abc" 'haha)
    (and #t #t #f #t )
}

;; ------ Or test ------
{
    (or)
    (or #t)
    (or #f)
    (or 1)
    (or 1 2 3)
    (or #f #t)
    (or 'yees 'nooo)
    (or "abc" '() 'nothing)
    (or '() 'a)
}

;; ------ Define test ------
{
    (define nil '())
    (define pass 'pass)
    (define true #t)
    (define false #f)
    (define one 1)
    (define hello "hello world")
    (set! hello 'hello)
    1
    ;;(if false 'this-should-not-happen 'pass)
    hello
    (set! hello "hello world again")
    hello
    one
    'nice
}

;; ------ Lambda Simple test ------
{
    (define l1 (lambda (a b c) a))
    (define l2 (lambda (a b c) (if a b c)))
    (define l3 (lambda (a b c) (lambda () '(a b c))))
    (define l4 (lambda (a b c) (set! a 1) (set! b '()) (set! c #t) c))
    (define l5 (lambda () 1 2 (if #t 'yes 'no)))
}

;; ------ Application test ------
{
    (l1 5 6 7) ;; => 5
    (l2 #t '(1 2 3) 'wrong) ;; => (1 2 3)
    (l2 #f '(1 2 3) 'this-should-be) ;; => 'this-should-be
    ((l3 1 2 3)) ;; => (a b c)
    (l4 1 2 3) ;; => #t
    (l5) ;; => 'yes
}

;; ------ Primitives test ------
(+ 1 2 3)