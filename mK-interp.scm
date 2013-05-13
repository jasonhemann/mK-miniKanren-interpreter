(load "./mk/mk.scm")
(load "./mk/numbers.ss")

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

#|

The following conventions are often used below:
  <g>* indicates a list of <g>
  <g>*s indicates a matrix of <g>, (really a list of <g>*)
  ge indicates a goal expression, when evaluated, it's simply a g (goal)

|#

(define empty-env '())

(define ext-env*o
  (lambda (x* a* env o)
    (fresh ()      
      (same-lengtho x* a*)
      (== `((env ,x* . ,a*) ,env) o))))

(define same-lengtho
  (lambda (l1 l2)
    (conde
      ((== '() l1) (== '() l2))
      ((fresh (a1 d1 a2 d2)
         (== `(,a1 . ,d1) l1)
         (== `(,a2 . ,d2) l2)
         (same-lengtho d1 d2))))))

(define ext-rec-env*o
  (lambda (x* a* env o)
    (fresh ()      
      (same-lengtho x* a*)    
      (== `((rec-env ,x* . ,a*) ,env) o))))

(define memo
  (lambda (x y*)
    (fresh (y d-y*)
      (== `(,y . ,d-y*) y*)
      (conde
        ((== x y))
        ((=/= x y)
         (memo x d-y*))))))

(define not-memo
  (lambda (x y*)
    (conde
      ((== '() y*))
      ((fresh (y d-y*)
         (== `(,y . ,d-y*) y*)
         (=/= x y)
         (not-memo x d-y*))))))

(define apply-ribo
  (lambda (y* a* x o)
    (fresh (y d-y*)
      (== `(,y . ,d-y*) y*)
      (fresh (a cdr-a*)        
        (== `(,a . ,cdr-a*) a*)
        (conde
          ((== y x) (== a o))
          ((=/= y x)
           (apply-ribo d-y* cdr-a* x o)))))))

(define scheme-forms
  '(lambda quote zero? sub1 * cons if letrec
    let list numexp))

(define scheme-formo
  (lambda (rator)
    (memo rator scheme-forms)))

(define mk-forms
  '(run run* == fresh conde project condu conda))

(define mk-formo
  (lambda (rator)
    (memo rator mk-forms)))

(define numexpo
  (lambda (ne)
    (fresh (n)
      (== `(numexp . ,n) ne))))

(define numvalo
  (lambda (nv)
    (fresh (n)
      (== `(numval . ,n) nv))))

(define num=o
  (lambda (nv1 nv2)
    (fresh (n)
      (== `(numval . ,n) nv1)
      (== `(numval . ,n) nv2))))

(define 0?o
  (lambda (n)
    (fresh (nv)
      (== `(numval . ,(build-num 0)) n))))

(define pos?o
  (lambda (n)
    (fresh (nv)
      (== `(numval . ,nv) n)
      (poso nv))))

(define monus1o
  (lambda (n o)
    (fresh (nv)
      (== `(numval . ,nv) n)
      (conde
        ((0?o n)
         (== n o))
        ((pos?o n)
         (fresh (n-)
           (minuso nv (build-num 1) n-)
           (== `(numval . ,n-) o)))))))

(define multo
  (lambda (n m o)
    (fresh (nv mv)
      (== `(numval . ,nv) n)
      (== `(numval . ,mv) m)
      (fresh (*nm)
        (*o nv mv *nm)
        (== `(numval . ,*nm) o)))))

(define car*o
  (lambda (a* o)
    (conde
      ((== '() a*) (== '() o))
      ((fresh (aa da d)
         (== `((,aa . ,da) . ,d) a*)
         (symbolo aa)
         (fresh (d^)
           (== `(,aa . ,d^) o)
           (car*o d d^)))))))

(define cadr*o
  (lambda (a* o)
    (conde
      ((== '() a*) (== '() o))
      ((fresh (aa ada d)
         (== `((,aa ,ada) . ,d) a*)
         (fresh (d^)
           (cadr*o d d^)
           (== `(,ada . ,d^) o)))))))

(define varo
  (lambda (name c o)
    (== `(var ,name . ,c) o)))

(define var*o
  (lambda (ls c o)
    (conde
      ((== '() ls) (== `(,c . ()) o))
      ((fresh (a d)
         (== `(,a . ,d) ls)
         (symbolo a)
         (fresh (va)
           (varo a c va)
           (fresh (c+)
             (pluso c (build-num 1) c+)
             (fresh (c++ vd)
               (var*o d c+ `(,c++ . ,vd))               
               (== `(,c++ ,va . ,vd) o)))))))))

(define var-eqo
  (lambda (x y o)
    (fresh (name1 name2 vid1 vid2)
      (== `(var ,name1 . ,vid1) x)
      (== `(var ,name2 . ,vid2) y)
      (conde
        ((== vid1 vid2) (== #t o))
        ((=/= vid1 vid2) (== #f o))))))

(define assqo
  (lambda (u S o)
    (conde
      ((== '() S) (== #f o))
      ((fresh (a d)
         (== `(,a . ,d) S)
         (fresh (aa da)
           (== `(,aa . ,da) a)
           (conde
             ((== u aa)
              (== a o))
             ((=/= u aa)
              (assqo u d o)))))))))

(define walko
  (lambda (u S o)
    (conde
      ((fresh (name vid)
         (== `(var ,name . ,vid) u)
         (fresh (v)
           (assqo u S v)
           (conde
             ((fresh (a d)
                (== `(,a . ,d) v)
                (walko d S o)))
             ((== v #f)
              (== u o))))))
      ((fresh (a d)
         (== `(,a . ,d) u)
         (=/= a 'var)
         (== u o)))
      ((not-pairo u)
       (== u o)))))

(define real-car?o
  (lambda (va)
    (fresh ()
      (=/= va 'var)
      (=/= va 'numval)
      (=/= va 'closure))))

(define walk*o
  (lambda (w s o)
    (fresh (v)
      (walko w s v)
      (conde
        ((fresh (name vid)
           (== `(var ,name . ,vid) v)
           (== v o)))
        ((fresh (nv)
           (== `(numval . ,nv) v)
           (== v o)))
        ((fresh (cl)
           (== `(closure . ,cl) v)
           (== v o)))
        ((fresh (a d)
           (== `(,a . ,d) v)
           (real-car?o a)
           (fresh (w*a w*d)
             (== `(,w*a . ,w*d) o)
             (walk*o a s w*a)
             (walk*o d s w*d))))
        ((not-pairo v) (== v o))))))

(define walk*-var*o
  (lambda (var* s o)
    (conde
      ((== '() var*)
       (== '() o))
      ((fresh (a d)
         (== `(,a . ,d) var*)
         (fresh (wa wd)
           (== `(,wa . ,wd) o)
           (walk*-var*o d s wd)
           (walk*o a s wa)))))))

(define ext-so
  (lambda (x v s o)
    (== `((,x . ,v) . ,s) o)))

(define var?o
  (lambda (x)
    (fresh (name xid)
      (== `(var ,name . ,xid) x))))

(define occurs-checko
  (lambda (x v^ s o)
    (fresh (v)
      (walko v^ s v)
      (conde
        ((fresh (name vid)
           (== `(var ,name . ,vid) v)
           (var-eqo v x o)))
        ((fresh (n)
           (== `(numval . ,n) v)
           (== #f o)))
        ((fresh (cl)
           (== `(closure . ,cl) v)
           (== #f o)))
        ((fresh (a d)
           (== `(,a . ,d) v)
           (real-car?o a)
           (fresh (oc-a)
             (occurs-checko x a s oc-a)
             (conde
               ((== #t oc-a)
                (== #t o))
               ((== #f oc-a)
                (occurs-checko x d s o))))))
        ((not-pairo v) (== #f o))))))

(define not-occurs-checko
  (lambda (x v s o)
    (fresh (oc)
      (occurs-checko x v s oc)
      (conde
        ((== oc #t) (== #f o))
        ((== oc #f) (== #t o))))))

(define ext-s-checko
  (lambda (x v s o)
    (fresh (noc)
      (not-occurs-checko x v s noc)
      (conde
        ((== noc #t) (ext-so x v s o))
        ((== noc #f) (== o #f))))))

(define mzeroo `(INC . (mzero-f)))

(define unito `(unit-goal))

(define choiceo
  (lambda (a/c f o)
    (== `(,a/c . ,f) o)))

(define apply-go
  (lambda (g s/c o)
    (conde
      [(== g `(unit-goal))
       (== `(INC . (unit-inc ,s/c)) o)]
      [(fresh (env^ ge*)
         (== g `(run-goal ,env^ ,ge*))
         (== `(INC . (run-inc ,env^ ,ge* ,s/c)) o))]
      [(fresh (u^ v^)
         (== g `(==-goal ,u^ ,v^))
         (== `(INC . (==-inc ,u^ ,v^ ,s/c)) o))]
      [(fresh (x* ge* env)
         (== g `(fresh-goal ,x* ,ge* ,env))
         (== `(INC . (fresh-inc ,x* ,ge* ,env ,s/c)) o))]
      [(fresh (ge*s env)
         (== g `(conde-goal ,ge*s ,env))
         (== `(INC . (conde-inc ,ge*s ,env ,s/c)) o))]
      [(fresh (x* ge* env)
         (== g `(project-goal ,x* ,ge* ,env))
         (== `(INC . (project-inc ,x* ,ge* ,env ,s/c)) o))]
      [(fresh (ge* ge*s g^ a/u env)
         (== g `(conda/u-goal ,ge* ,ge*s ,g^ ,a/u ,env))
         (== `(INC . (conda/u-inc ,ge* ,ge*s ,g^ ,a/u ,env ,s/c)) o))]
      [(fresh (env ge*)
         (== g `(conj-goal ,env ,ge*))
         (== `(INC . (conj-inc ,env ,ge* ,s/c)) o))])))

(define in-envo
  (lambda (env rator) 
    (conde
      ((fresh (y* a* env^)
         (== `((env ,y* . ,a*) ,env^) env)
         (conde
           ((memo rator y*))
           ((not-memo rator y*)
            (in-envo env^ rator)))))
      ((fresh (y* a* env^)
         (== `((rec-env ,y* . ,a*) ,env^) env)
         (conde
           ((memo rator y*))
           ((not-memo rator y*)
            (in-envo env^ rator))))))))

(define not-in-envo
  (lambda (env rator)
    (conde
      ((== '() env))
      ((fresh (y* a* env^)
         (== `((env ,y* . ,a*) ,env^) env)
         (not-memo rator y*)
         (not-in-envo env^ rator)))
      ((fresh (y* a* env^)
         (== `((rec-env ,y* . ,a*) ,env^) env)
         (not-memo rator y*)
         (not-in-envo env^ rator))))))

(define unifyo
  (lambda (u^ v^ S o)
    (fresh (u v)
      (walko u^ S u)
      (walko v^ S v)
      (conde
        ((fresh (a d)
           (== `(,a . ,d) u)
           (conde
             ((== a 'var)
              (conde
                ((fresh (va vd)
                   (== `(,va . ,vd) v)
                   (conde
                     ((== u v) (== S o))
                     ((== va 'var) (=/= d vd) (ext-so u v S o))
                     ((=/= va 'var) (unifyo v u S o)))))
                ((not-pairo v) (unifyo v u S o))))
             ((== a 'numval)
              (conde
                ((fresh (va vd)
                   (== `(,va . ,vd) v)
                   (conde
                     ((== va 'var) (ext-so v u S o))
                     ((== u v) (== S o))
                     ((== va 'numval) (=/= d vd) (== #f o))
                     ((== va 'closure) (== #f o))
                     ((real-car?o va) (== #f o)))))
                ((not-pairo v) (== #f o))))
             ((== a 'closure)
              (conde
                ((fresh (va vd)
                   (== `(,va . ,vd) v)
                   (conde
                     ((== va 'var) (ext-so v u S o))
                     ((=/= va 'var) (== #f o)))))
                ((not-pairo v) (== #f o))))
             ((real-car?o a)
              (conde
                ((fresh (va vd)
                   (== `(,va . ,vd) v)
                   (conde
                     ((== va 'var) (ext-s-checko v u S o))
                     ((== va 'numval) (== #f o))
                     ((== va 'closure) (== #f o))
                     ((real-car?o va)
                      (fresh (S^)
                        (unifyo a va S S^)
                        (conde
                          ((== #f S^) (== #f o))
                          ((=/= #f S^)
                           (unifyo d vd S^ o))))))))
                ((not-pairo v) (== #f o)))))))
        ((not-pairo u)
         (conde
           ((fresh (va vd)
              (== `(,va . ,vd) v)
              (conde
                ((== va 'var) (ext-so v u S o))
                ((=/= va 'var) (== #f o)))))
           ((== u v) (== S o))
           ((not-pairo v) (=/= u v) (== #f o))))))))

(define value-ofo
  (lambda (exp o)
    (eval-expo exp empty-env o)))

(define run-fno
  (lambda (nexp x ge* env o)
    (fresh (n x-var)
      (eval-expo nexp env n)
      (varo x 0 x-var)
      (fresh (env^)
        (ext-env*o `(,x) `(,x-var) env env^)
        (takeo n `(INC . (run-fn-f (run-goal ,env^ ,ge*))) o)))))

(define apply-envo
  (lambda (env x o)
    (conde
      ((fresh (y* a* env^)
         (== `((env ,y* . ,a*) ,env^) env)
         (conde
           ((memo x y*) (apply-ribo y* a* x o))
           ((not-memo x y*) (apply-envo env^ x o)))))
      ((fresh (y* a* env^)
         (== `((rec-env ,y* . ,a*) ,env^) env)
         (conde
           ((memo x y*) (fresh (lam-exp)
                          (apply-ribo y* a* x lam-exp)
                          (eval-expo lam-exp env o)))
           ((not-memo x y*) (apply-envo env^ x o))))))))

(define apply-INCo
  (lambda (f o)
    (fresh (f^)
      (== `(INC . ,f^) f)
      (conde
        ((== '(mzero-f) f^)
         (== '() o))
        ((fresh (s/c)
           (== `(unit-inc ,s/c) f^)
           (== `(,s/c . ,mzeroo) o)))
        ((fresh (env^ ge* s/c)
           (== `(run-inc ,env^ ,ge* ,s/c) f^)
           (apply-go `(conj-goal ,env^ ,ge*) s/c o)))
        ((fresh (u v s c)
           (== `(==-inc ,u ,v (,s . ,c)) f^)
           (fresh (ans)
             (unifyo u v s ans)
             (conde
               ((=/= #f ans)
                (apply-go unito `(,ans . ,c) o))
               ((== #f ans)
                (apply-INCo mzeroo o))))))
        ((fresh (x* ge* env s c)
           (== `(fresh-inc ,x* ,ge* ,env (,s . ,c)) f^)
           (fresh (c+ var*)
             (var*o x* c `(,c+ . ,var*))
             (fresh (env^)
               (ext-env*o x* var* env env^)
               (apply-go `(conj-goal ,env^ ,ge*) `(,s . ,c+) o)))))
        ((fresh (ge*s env s/c)
           (== `(conde-inc ,ge*s ,env ,s/c) f^)
           (mplus*so ge*s s/c env o)))
        ((fresh (x* ge* env s c)
           (== `(project-inc ,x* ,ge* ,env (,s . ,c)) f^)
           (fresh (xvar*)
             (eval-exp*o x* env xvar*)
             (fresh (val*)
               (walk*-var*o xvar* s val*)
               (fresh (env^)                 
                 (ext-env*o xvar* val* env env^)
                 (apply-go `(conj-goal ,env^ ,ge*) `(,s . ,c) o))))))
        ((fresh (ge* ge*s g^ a/u env s/c)
           (== `(conda/u-inc ,ge* ,ge*s ,g^ ,a/u ,env ,s/c) f^)
           (fresh (a-inf)
               (apply-go g^ s/c a-inf)
               (conda/u-helpo a-inf ge* ge*s a/u env s/c o))))
        ((fresh (env ge* s/c)
           (== `(conj-inc ,env ,ge* ,s/c) f^)
           (conde
             ((== '() ge*) (apply-go unito s/c o))
             ((fresh (ge)
                (== `(,ge) ge*)
                (fresh (g)
                  (eval-expo ge env g)
                  (apply-go g s/c o))))
             ((fresh (ge d-ge*)
                (== `(,ge . ,d-ge*) ge*)
                (=/= '() d-ge*)
                (fresh (g)
                  (eval-expo ge env g)
                  (fresh (a-inf)
                    (apply-go g s/c a-inf)
                    (bind*o a-inf d-ge* env o))))))))
        ((fresh (g)
           (== `(run-fn-f ,g) f^)
           (apply-go g `(() . ,(build-num 1)) o)))
        ((fresh (a-inf ge* ge*s a/u env s/c)
           (== `(conda/u-goal-f ,a-inf ,ge* ,ge*s ,a/u ,env ,s/c) f^)
           (fresh (a-inf^)
             (apply-INCo a-inf a-inf^)
             (conda/u-helpo a-inf^ ge* ge*s a/u env s/c o))))
        ((fresh (a-inf g)
           (== `(bind-1-f ,a-inf ,g) f^)
           (fresh (a-inf^)
             (apply-INCo a-inf a-inf^)
             (bindo a-inf^ g o))))
        ((fresh (f g) 
           (== `(bind-2-f ,f ,g) f^)
           (fresh (a-inf^^)
             (apply-INCo f a-inf^^)
             (bindo a-inf^^ g o))))
        ((fresh (f a-inf)
           (== `(mplus-1-f ,f ,a-inf) f^)
           (fresh (a-inf^)
             (apply-INCo f a-inf^)
             (mpluso a-inf^ a-inf o))))
        ((fresh (f d)
           (== `(mplus-2-f ,f ,d) f^)
           (fresh (a-inf^)
             (apply-INCo f a-inf^)
             (mpluso a-inf^ d o))))
        ((fresh (d-ge* s env)
           (== `(mplus*-f ,d-ge* ,s ,env) f^)
           (mplus*o d-ge* s env o)))
        ((fresh (d-ge*s s env)
           (== `(mplus*s-f ,d-ge*s ,s ,env) f^)
           (mplus*so d-ge*s s env o)))))))

(define conda/u-helpo
  (lambda (a-inf ge* ge*s a/u env s/c o)
    (conde
      ((== '() a-inf)
       (conde
         ((== '() ge*s) (apply-INCo mzeroo o))
         ((fresh (aa da d)
            (== `((,aa . ,da) . ,d) ge*s)
            (fresh (g)
              (eval-expo aa env g)
              (fresh (a-inf^)                                                     
                (apply-go g s/c a-inf^)
                (conda/u-helpo a-inf^ da d a/u env s/c o)))))))
      ((fresh (p)
         (== `(INC . ,p) a-inf)
         (== `(INC . (conda/u-goal-f ,a-inf ,ge* ,ge*s ,a/u ,env ,s/c)) o)))
      ((fresh (a d)
         (== `(,a . ,d) a-inf)
         (=/= a 'INC)
         (conde
           ((== a/u 'a) (bind*o a-inf ge* env o))
           ((== a/u 'u) (fresh (car-a-inf)
                          (caro a-inf car-a-inf)
                          (fresh (a-inf^)
                            (apply-go unito car-a-inf a-inf^)
                            (bind*o a-inf^ ge* env o))))))))))

(define eval-exp*o
  (lambda (exp* env o)
    (conde
      ((== '() exp*)
       (== '() o))
      ((fresh (e e*)
         (== `(,e . ,e*) exp*)
         (fresh (v v*)    
           (eval-exp*o e* env v*)
           (eval-expo e env v)
           (== `(,v . ,v*) o)))))))

(define eval-expo
  (lambda (exp env o)
    (conde
      ((== exp #t) (== o #t))
      ((== exp #f) (== o #f))
      ((symbolo exp) (apply-envo env exp o))
      ((fresh (rator rand*)
         (== `(,rator . ,rand*) exp)
         (symbolo rator)
         (in-envo env rator)
         (fresh (v-rator v-rand*)
           (apply-envo env rator v-rator)           
           (eval-exp*o rand* env v-rand*)
           (apply-closureo v-rator v-rand* o))))
      ((fresh (rator rand*)
         (== `(,rator . ,rand*) exp)
         (symbolo rator)
         (not-in-envo env rator)
         (eval-exp-special-formo exp env o)))
      ((fresh (rator rand*)
         (== `(,rator . ,rand*) exp)
         (fresh (a d)
           (== `(,a . ,d) rator)
           (fresh (cl args)
             (eval-expo rator env cl)
             (eval-exp*o rand* env args)
             (apply-closureo cl args o))))))))

(define apply-closureo
  (lambda (cl a* o)
    (fresh (x* body env)
      (== `(closure ,x* ,body ,env) cl)
      (fresh (env^)
        (ext-env*o x* a* env env^)
        (eval-expo body env^ o)))))

(define eval-exp-special-formo
  (lambda (exp env o)
    (fresh (tag rest)
      (== `(,tag . ,rest) exp)
      (conde
        ((scheme-formo tag)
         (eval-exp-scheme-formo exp env o))
        ((mk-formo tag)
         (eval-mko exp env o))))))

(define tags
  '(numval closure run-goal ==-goal
    fresh-goal run-goal conde-goal project-goal
    conda/u-goal conj-goal unit-goal))

(define legal-termo
  (lambda (t)
    (conde
      ((not-pairo t)
       (not-a-tago t tags))
      ((fresh (a d)
	 (== `(,a . ,d) t)
	 (not-a-tago a tags))))))

(define not-a-tago
  (lambda (nt t*)
    (conde
      ((== '() t*))
      ((fresh (t d-t*)
	 (== `(,t . ,d-t*) t*)
	 (=/= t nt)
	 (not-a-tago nt d-t*))))))

(define eval-exp-scheme-formo
  (lambda (exp env o)
    (conde
      ((fresh (ne)
         (== `(numexp . ,ne) exp)
         (== `(numval . ,ne) o)))
      ((fresh (e*)
         (== `(list . ,e*) exp)
	 (eval-exp*o e* env o)
         (legal-termo o)))
      ((fresh (x* body)
         (== `(lambda ,x* ,body) exp)
         (== `(closure ,x* ,body ,env) o)))
      ((fresh (val)
         (== `(quote ,val) exp)
	 (legal-termo val)
         (== val o)))
      ((fresh (e)
         (== `(zero? ,e) exp)
         (fresh (nv)
           (eval-expo e env nv)
	   (fresh (n)	     
	     (== `(numval . ,n) nv)
	     (conde
	       ((== (build-num 0) n) (== #t o))
	       ((=/= (build-num 0) n) (== #f o)))))))
      ((fresh (e)
         (== `(sub1 ,e) exp)
         (fresh (nv)
           (eval-expo e env nv)
           (monus1o nv o))))
      ((fresh (ne me)
         (== `(* ,ne ,me) exp)
         (fresh (nv mv)
           (eval-expo ne env nv)
           (eval-expo me env mv)
           (multo nv mv o))))
      ((fresh (e1 e2)
         (== `(cons ,e1 ,e2) exp)
         (fresh (ve1 ve2)
           (== `(,ve1 . ,ve2) o)
           (eval-expo e1 env ve1)
           (eval-expo e2 env ve2)
	   (not-a-tago ve1 tags))))
      ((fresh (te ce ae)
         (== `(if ,te ,ce ,ae) exp)
         (fresh (vte)
           (eval-expo te env vte)
           (conde
             ((== vte #f) (eval-expo ae env o))
             ((=/= vte #f) (eval-expo ce env o))))))
      ((fresh (def* body)
         (== `(letrec ,def* ,body) exp)
         (fresh (x* a*)
           (car*o def* x*)
           (cadr*o def* a*)
           (fresh (env^)
             (ext-rec-env*o x* a* env env^)
             (eval-expo body env^ o)))))
      ((fresh (def* body)
         (== `(let ,def* ,body) exp)
         (fresh (var* val*)
           (car*o def* var*)
           (eval-exp-cadr*o def* env val*)
           (fresh (env^)
             (ext-env*o var* val* env env^)
             (eval-expo body env^ o))))))))

(define eval-mko
  (lambda (exp env o)
    (conde
      ((fresh (nexp x ge*)
         (== `(run ,nexp (,x) . ,ge*) exp)
         (run-fno nexp x ge* env o)))
      ((fresh (x ge*)
         (== `(run* (,x) . ,ge*) exp)
         (run-fno #f x ge* env o)))
      ((fresh (u v)
         (== `(== ,u ,v) exp)
         (fresh (u^ v^)
           (eval-expo u env u^)
           (eval-expo v env v^)
           (== `(==-goal ,u^ ,v^) o))))
      ((fresh (x* ge*)
         (== `(fresh ,x* . ,ge*) exp)
         (== `(fresh-goal ,x* ,ge* ,env) o)))
      ((fresh (ge*s)
         (== `(conde . ,ge*s) exp)
         (== `(conde-goal ,ge*s ,env) o)))
      ((fresh (x* ge*)
         (== `(project ,x* . ,ge*) exp)
         (== `(project-goal ,x* ,ge* ,env) o)))
      ((fresh (ge ge* ge*s)
         (== `(conda (,ge . ,ge*) . ,ge*s) exp)
         (fresh (g)
           (eval-expo ge env g)
           (== `(conda/u-goal ,ge* ,ge*s ,g a ,env) o))))
      ((fresh (ge ge* ge*s)
         (== `(condu (,ge . ,ge*) . ,ge*s) exp)
         (fresh (g)
           (eval-expo ge env g)
         (== `(conda/u-goal ,ge* ,ge*s ,g u ,env) o)))))))

(define eval-exp-cadr*o
  (lambda (def* env o)
    (conde
      ((== def* '())
       (== '() o))
      ((fresh (aa ada d)
         (== `((,aa ,ada) . ,d) def*)
         (fresh (a^ d^)
           (eval-exp-cadr*o d env d^)
           (eval-expo ada env a^)
           (== `(,a^ . ,d^) o)))))))

(define takeo
  (lambda (n f o)
    (conde
      ((== `(numval . ,(build-num 0)) n)
       (== '() o))
      ((conde
         ((== n #f))
         ((pos?o n)))
       (fresh (a-inf)
         (apply-INCo f a-inf)
         (conde
           ((== '() a-inf) (== '() o))
           ((fresh (p)
              (== `(INC . ,p) a-inf)
              (takeo n a-inf o)))
           ((fresh (a c d)
              (== `((,a . ,c) . ,d) a-inf)
              (conde
                ((fresh (nv)
                   (== `(numval . ,nv) n)
                   (fresh (n-)
                     (monus1o n n-)
                     (fresh (d^)
                       (takeo n- d d^)
                       (== `(,a . ,d^) o)))))
                ((== #f n)
                 (fresh (d^)
                   (takeo #f d d^)
                   (== `(,a . ,d^) o))))))))))))

(define bindo
  (lambda (a-inf g o)
    (conde
      ((== '() a-inf) (apply-INCo mzeroo o))
      ((fresh (p)
         (== `(INC . ,p) a-inf)
         (== `(INC . (bind-1-f ,a-inf ,g)) o)))
      ((fresh (a f)
         (== `(,a . ,f) a-inf) 
         (=/= 'INC a) 
         (fresh (a-inf^)
           (apply-go g a a-inf^)
           (mpluso a-inf^ `(INC . (bind-2-f ,f ,g)) o))))))) 

(define bind*o
  (lambda (a-inf ge* env o)
    (conde
      ((== '() ge*) (== a-inf o))
      ((fresh (a d)
         (== `(,a . ,d) ge*)
         (fresh (g)
           (eval-expo a env g)
           (fresh (a-inf^)
             (bindo a-inf g a-inf^)
             (bind*o a-inf^ d env o))))))))

(define mpluso
  (lambda (a-inf f o)
    (conde
      ((== '() a-inf) (apply-INCo f o))
      ((fresh (p)
         (== `(INC . ,p) a-inf)
         (== `(INC . (mplus-1-f ,f ,a-inf)) o)))
      ((fresh (a d)
         (== `(,a . ,d) a-inf)
         (=/= 'INC a)
         (choiceo a `(INC . (mplus-2-f ,f ,d)) o))))))

(define mplus*o
  (lambda (ge* s env o)
    (conde
      ((== '() ge*) (apply-INCo mzeroo o))
      ((fresh (ge)
         (== `(,ge) ge*)
         (fresh (g)
           (eval-expo ge env g)
           (apply-go g s o))))
      ((fresh (ge d-ge*)
         (== `(,ge . ,d-ge*) ge*)
         (=/= '() d-ge*)
         (fresh (g)
           (eval-expo ge env g)
           (fresh (a-inf)
             (apply-g g s a-inf)
             (mpluso a-inf
             `(INC . (mplus*-f ,d-ge* ,s ,env)) o))))))))

(define mplus*so
  (lambda (ge*s s env o)
    (conde
      ((== '() ge*s)
       (apply-INCo mzeroo o))
      ((fresh (ge*)
         (== `(,ge*) ge*s)
         (conde
           ((== '() ge*) (apply-go unito s o))
           ((fresh (ge d-ge*)
              (== `(,ge . ,d-ge*) ge*)
              (fresh (g)
                (eval-expo ge env g)
                (fresh (a-inf)
                  (apply-go g s a-inf)
                  (bind*o a-inf d-ge* env o))))))))
      ((fresh (d-ge*s)
         (== `(() . ,d-ge*s) ge*s)
         (=/= '() d-ge*s)         
         (mplus*so d-ge*s s env o)))
      ((fresh (ge d-ge* d-ge*s)
         (== `((,ge . ,d-ge*) . ,d-ge*s) ge*s)
         (=/= '() d-ge*s)
         (fresh (g)
           (eval-expo ge env g)
           (fresh (a-inf)
             (apply-go g s a-inf)
             (fresh (a-inf^)
               (bind*o a-inf d-ge* env a-inf^)
               (mpluso a-inf^ `(INC . (mplus*s-f ,d-ge*s ,s ,env)) o)))))))))

;; test-suite 

(test-check "memo 10"
  (run 10 (q) (fresh (x y*) (memo x y*) (== q `(,x ,y*))))
  '((_.0 (_.0 . _.1)) ((_.0 (_.1 _.0 . _.2)) (=/= ((_.0 _.1))))
    ((_.0 (_.1 _.2 _.0 . _.3)) (=/= ((_.0 _.1)) ((_.0 _.2))))
    ((_.0 (_.1 _.2 _.3 _.0 . _.4))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3))))
    ((_.0 (_.1 _.2 _.3 _.4 _.0 . _.5))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.0 . _.6))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))
          ((_.0 _.5))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.0 . _.7))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))
          ((_.0 _.5)) ((_.0 _.6))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7 _.0 . _.8))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))
          ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.0 . _.9))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))
          ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9 _.0 . _.10))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))
          ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8))
          ((_.0 _.9))))))

(test-check "not-memo 10"
  (run 10 (q) (fresh (x y*) (not-memo x y*) (== q `(,x ,y*))))
  '((_.0 ()) ((_.0 (_.1)) (=/= ((_.0 _.1))))
    ((_.0 (_.1 _.2)) (=/= ((_.0 _.1)) ((_.0 _.2))))
    ((_.0 (_.1 _.2 _.3))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3))))
    ((_.0 (_.1 _.2 _.3 _.4))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))
          ((_.0 _.5))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))
          ((_.0 _.5)) ((_.0 _.6))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))
          ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))
          ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8))))
    ((_.0 (_.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 _.9))
     (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 _.4))
          ((_.0 _.5)) ((_.0 _.6)) ((_.0 _.7)) ((_.0 _.8))
          ((_.0 _.9))))))

(test-check "apply-ribo 5"
  (run 5 (q) (fresh (y* a* x o) (apply-ribo y* a* x o) (== q `(,y* ,a* ,x ,o))))
  '(((_.0 . _.1) (_.2 . _.3) _.0 _.2)
    (((_.0 _.1 . _.2) (_.3 _.4 . _.5) _.1 _.4)
     (=/= ((_.0 _.1))))
    (((_.0 _.1 _.2 . _.3) (_.4 _.5 _.6 . _.7) _.2 _.6)
     (=/= ((_.0 _.2)) ((_.1 _.2))))
    (((_.0 _.1 _.2 _.3 . _.4) (_.5 _.6 _.7 _.8 . _.9) _.3 _.8)
     (=/= ((_.0 _.3)) ((_.1 _.3)) ((_.2 _.3))))
    (((_.0 _.1 _.2 _.3 _.4 . _.5)
      (_.6 _.7 _.8 _.9 _.10 . _.11)
      _.4
      _.10)
     (=/= ((_.0 _.4)) ((_.1 _.4)) ((_.2 _.4)) ((_.3 _.4))))))

(test-check "scheme-formo"
  (run* (q) (scheme-formo q))
  '(lambda quote zero? sub1 * cons if letrec let list numexp))

(test-check "mk-formo"
  (run* (q) (mk-formo q))
  '(run run* == fresh conde project condu conda))

(test-check "numexpo"
  (run* (q) (numexpo q))
  '((numexp . _.0)))

(test-check "numvalo"
  (run* (q) (numvalo q))
  '((numval . _.0)))

(test-check "num=o"
  (run* (q)
    (fresh (nv1 nv2)
      (num=o nv1 nv2)
      (== q `(,nv1 ,nv2))))
  '(((numval . _.0) (numval . _.0))))

(test-check "0?o"
  (run* (q) (0?o q))
  '((numval)))

(test-check "pos?o"
  (run* (q) (pos?o q))
  '((numval _.0 . _.1)))

(test-check "monus1o 5"
  (run 5 (q) (fresh (a b) (monus1o a b) (== q `(,a ,b))))
  '(((numval) (numval))
    ((numval 1) (numval))
    ((numval 0 1) (numval 1))
    ((numval 1 _.0 . _.1) (numval 0 _.0 . _.1))
    ((numval 0 0 1) (numval 1 1))))

(test-check "mult numbers"
  (run 1 (q)
    (fresh (qv)
      (multo '(numval . (1)) '(numval . (1)) q)))
  '((numval 1)))

(test-check "multo 10"
  (run 10 (q) (fresh (n m o) (multo n m o) (== q `(,n ,m ,o))))
  '(((numval) (numval . _.0) (numval)) ((numval _.0 . _.1) (numval) (numval))
    ((numval 1) (numval _.0 . _.1) (numval _.0 . _.1))
    ((numval _.0 _.1 . _.2) (numval 1) (numval _.0 _.1 . _.2))
    ((numval 0 1)
     (numval _.0 _.1 . _.2)
     (numval 0 _.0 _.1 . _.2))
    ((numval 0 0 1)
     (numval _.0 _.1 . _.2)
     (numval 0 0 _.0 _.1 . _.2))
    ((numval 1 _.0 . _.1) (numval 0 1) (numval 0 1 _.0 . _.1))
    ((numval 0 0 0 1)
     (numval _.0 _.1 . _.2)
     (numval 0 0 0 _.0 _.1 . _.2))
    ((numval 1 _.0 . _.1)
     (numval 0 0 1)
     (numval 0 0 1 _.0 . _.1))
    ((numval 0 1 _.0 . _.1)
     (numval 0 1)
     (numval 0 0 1 _.0 . _.1))))

(test-check "car*o"
  (run 4 (q)
       (fresh (a b)
         (car*o a b)
         (== `(,a ,b) q)))
  '((() ())
    ((((_.0 . _.1)) (_.0)) (sym _.0))
    ((((_.0 . _.1) (_.2 . _.3)) (_.0 _.2)) (sym _.0 _.2))
    ((((_.0 . _.1) (_.2 . _.3) (_.4 . _.5)) (_.0 _.2 _.4)) (sym _.0 _.2 _.4))))

(test-check "cadr*o"
  (run 4 (q)
    (fresh (a b)
      (cadr*o a b)
      (== `(,a ,b) q)))
  '((() ())
    (((_.0 _.1)) (_.1))
    (((_.0 _.1) (_.2 _.3)) (_.1 _.3))
    (((_.0 _.1) (_.2 _.3) (_.4 _.5)) (_.1 _.3 _.5))))

(test-check "varo"
  (run* (q) (fresh (a b) (varo a b q)))
  '((var _.0 . _.1)))

(test-check "var*o 5"
  (run 5 (q) (fresh (a b c) (var*o a b c) (== `(,a ,b ,c) q)))
  '((() _.0 (_.0))
    (((_.0) () ((1) (var _.0))) (sym _.0))
    (((_.0) (1) ((0 1) (var _.0 1))) (sym _.0))
    (((_.0 _.1) () ((0 1) (var _.0) (var _.1 1))) (sym _.0 _.1))
    (((_.0 _.1 _.2) () ((1 1) (var _.0) (var _.1 1) (var _.2 0 1)))
     (sym _.0 _.1 _.2))))

(test-check "var-eqo"
  (run* (q) (fresh (a b c) (var-eqo a b c) (== q `(,a ,b ,c))))
  '(((var _.0 . _.1) (var _.2 . _.1) #t)
    (((var _.0 . _.1) (var _.2 . _.3) #f) (=/= ((_.1 _.3))))))

(test-check "assqo 5"
  (run 5 (q) (fresh (a b c) (assqo a b c) (== `(,a ,b ,c) q)))
  '((_.0 () #f)
    (_.0 ((_.0 . _.1) . _.2) (_.0 . _.1))
    ((_.0 ((_.1 . _.2)) #f) (=/= ((_.0 _.1))))
    ((_.0 ((_.1 . _.2) (_.0 . _.3) . _.4) (_.0 . _.3)) (=/= ((_.0 _.1))))
    ((_.0 ((_.1 . _.2) (_.3 . _.4)) #f) (=/= ((_.0 _.1)) ((_.0 _.3))))))

(test-check "walko 5"
  (run 5 (q) (fresh (a b c) (walko a b c) (== `(,a ,b ,c) q)))
  '(((_.0 _.1 _.0) (not-pair _.0))
    (((_.0 . _.1) _.2 (_.0 . _.1)) (=/= ((_.0 var))))
    ((var _.0 . _.1) () (var _.0 . _.1))
    (((var _.0 . _.1) ((_.2 . _.3)) (var _.0 . _.1)) (=/= ((_.2 (var _.0 . _.1)))))
    (((var _.0 . _.1) (((var _.0 . _.1) . _.2) . _.3) _.2) (not-pair _.2))))

(test-check "walk*o 10"
  (run 10 (q) (fresh (a b c) (walk*o a b c) (== `(,a ,b ,c) q)))
  '(((_.0 _.1 _.0) (not-pair _.0))
    ((numval . _.0) _.1 (numval . _.0))
    ((closure . _.0) _.1 (closure . _.0))
    ((var _.0 . _.1) () (var _.0 . _.1))
    (((var _.0 . _.1) ((_.2 . _.3)) (var _.0 . _.1)) (=/= ((_.2 (var _.0 . _.1)))))
    (((var _.0 . _.1) (((var _.0 . _.1) . _.2) . _.3) _.2) (not-pair _.2))
    ((var _.0 . _.1) (((var _.0 . _.1) numval . _.2) . _.3) (numval . _.2))
    ((var _.0 . _.1) (((var _.0 . _.1) closure . _.2) . _.3) (closure . _.2))
    (((_.0 . _.1) _.2 (_.0 . _.1)) (=/= ((_.0 closure)) ((_.0 numval)) ((_.0 var))) (not-pair _.0 _.1))
    (((_.0 numval . _.1) _.2 (_.0 numval . _.1)) (=/= ((_.0 closure)) ((_.0 numval)) ((_.0 var))) (not-pair _.0))))

(test-check "test-walk"
  (run 10 (q) 
    (fresh (a b c) 
      (walk*o '(var a . (1))
              '(((var a . (1 1)) . (numval . (1 1)))
                ((var a . (0 1)) . (numval . (0 1)))
                ((var a . (1)) . (numval . (1))))
              q)))
  '((numval 1)))

(test-check "ext-so"
  (run* (q)
    (fresh (x v s o)
      (ext-so x v s o)
      (== q `(,x ,v ,s ,o))))
  '((_.0 _.1 _.2 ((_.0 . _.1) . _.2))))

(test-check "walk*-var*o 10"
  (run 10 (q) (fresh (a b c) (walk*-var*o a b c) (== `(,a ,b ,c) q)))
  '((() _.0 ())
    (((_.0) _.1 (_.0)) (not-pair _.0))
    (((numval . _.0)) _.1 ((numval . _.0)))
    (((closure . _.0)) _.1 ((closure . _.0)))
    (((var _.0 . _.1)) () ((var _.0 . _.1)))
    (((_.0 _.1) _.2 (_.0 _.1)) (not-pair _.0 _.1))
    ((((var _.0 . _.1)) ((_.2 . _.3)) ((var _.0 . _.1))) (=/= ((_.2 (var _.0 . _.1)))))
    ((((numval . _.0) _.1) _.2 ((numval . _.0) _.1)) (not-pair _.1))
    ((((closure . _.0) _.1) _.2 ((closure . _.0) _.1)) (not-pair _.1))
    ((((var _.0 . _.1)) (((var _.0 . _.1) . _.2) . _.3) (_.2)) (not-pair _.2))))

(test-check "var?o"
  (run* (q) (var?o q))
  '((var _.0 . _.1)))

(test-check "occurs-checko 5"
  (run 5 (q) (fresh (x v^ s o) (occurs-checko x v^ s o) (== `(,x ,v^ ,s ,o) q)))
  '(((_.0 _.1 _.2 #f) (not-pair _.1))
    (_.0 (numval . _.1) _.2 #f)
    (_.0 (closure . _.1) _.2 #f)
    ((var _.0 . _.1) (var _.2 . _.1) () #t)
    (((var _.0 . _.1) (var _.2 . _.3) () #f) (=/= ((_.1 _.3))))))

(test-check "occurs-check success (failure)"
  (run* (q) (occurs-checko '(var a . ())
                           '((numval . ()) . (var b . ()))
                           '()
                           q))
  '(#t))

(test-check "not-occurs-checko 5"
  (run 5 (q) (fresh (x v^ s o) (not-occurs-checko x v^ s o) (== `(,x ,v^ ,s ,o) q)))
  '(((_.0 _.1 _.2 #t) (not-pair _.1))
    (_.0 (numval . _.1) _.2 #t)
    (_.0 (closure . _.1) _.2 #t)
    ((var _.0 . _.1) (var _.2 . _.1) () #f)
    (((var _.0 . _.1) (var _.2 . _.3) () #t) (=/= ((_.1 _.3))))))

(test-check "ext-s-checko"
  (run 5 (q) (fresh (x v^ s o) (ext-s-checko x v^ s o) (== `(,x ,v^ ,s ,o) q)))
  '(((_.0 _.1 _.2 ((_.0 . _.1) . _.2)) (not-pair _.1))
    (_.0 (numval . _.1) _.2 ((_.0 numval . _.1) . _.2))
    (_.0 (closure . _.1) _.2 ((_.0 closure . _.1) . _.2))
    ((var _.0 . _.1) (var _.2 . _.1) () #f)
    (((var _.0 . _.1) (var _.2 . _.3) () (((var _.0 . _.1) var _.2 . _.3))) (=/= ((_.1 _.3))))))

(test-check "apply-go"
  (run* (q) (fresh (x v^ s) (apply-go x v^ s) (== `(,x ,v^ ,s) q)))
  '(((unit-goal) _.0 (INC unit-inc _.0))
    ((run-goal _.0 _.1) _.2 (INC run-inc _.0 _.1 _.2))
    ((==-goal _.0 _.1) _.2 (INC ==-inc _.0 _.1 _.2))
    ((fresh-goal _.0 _.1 _.2) _.3 (INC fresh-inc _.0 _.1 _.2 _.3))
    ((conde-goal _.0 _.1) _.2 (INC conde-inc _.0 _.1 _.2))
    ((project-goal _.0 _.1 _.2) _.3 (INC project-inc _.0 _.1 _.2 _.3))
    ((conda/u-goal _.0 _.1 _.2 _.3 _.4) _.5 (INC conda/u-inc _.0 _.1 _.2 _.3 _.4 _.5))
    ((conj-goal _.0 _.1) _.2 (INC conj-inc _.0 _.1 _.2))))

(test-check "in-envo  10"
  (run 10 (q) (fresh (x v^) (in-envo x v^) (== `(,x ,v^) q)))
  '((((env (_.0 . _.1) . _.2) _.3) _.0)
    (((rec-env (_.0 . _.1) . _.2) _.3) _.0)
    ((((env (_.0 _.1 . _.2) . _.3) _.4) _.1) (=/= ((_.0 _.1))))
    ((((rec-env (_.0 _.1 . _.2) . _.3) _.4) _.1)
     (=/= ((_.0 _.1))))
    ((((env (_.0 _.1 _.2 . _.3) . _.4) _.5) _.2)
     (=/= ((_.0 _.2)) ((_.1 _.2))))
    ((((rec-env (_.0 _.1 _.2 . _.3) . _.4) _.5) _.2)
     (=/= ((_.0 _.2)) ((_.1 _.2))))
    ((((env (_.0 _.1 _.2 _.3 . _.4) . _.5) _.6) _.3)
     (=/= ((_.0 _.3)) ((_.1 _.3)) ((_.2 _.3))))
    ((((rec-env (_.0 _.1 _.2 _.3 . _.4) . _.5) _.6) _.3)
     (=/= ((_.0 _.3)) ((_.1 _.3)) ((_.2 _.3))))
    ((((env (_.0 _.1 _.2 _.3 _.4 . _.5) . _.6) _.7) _.4)
     (=/= ((_.0 _.4)) ((_.1 _.4)) ((_.2 _.4)) ((_.3 _.4))))
    ((((rec-env (_.0 _.1 _.2 _.3 _.4 . _.5) . _.6) _.7) _.4)
     (=/= ((_.0 _.4)) ((_.1 _.4)) ((_.2 _.4)) ((_.3 _.4))))))

(test-check "not-in-envo 10"
  (run 10 (q) (fresh (x v^) (not-in-envo x v^) (== `(,x ,v^) q)))
  '((() _.0)
    (((env () . _.0) ()) _.1)
    (((rec-env () . _.0) ()) _.1)
    ((((env (_.0) . _.1) ()) _.2) (=/= ((_.0 _.2))))
    ((((rec-env (_.0) . _.1) ()) _.2) (=/= ((_.0 _.2))))
    (((env () . _.0) ((env () . _.1) ())) _.2)
    (((rec-env () . _.0) ((env () . _.1) ())) _.2)
    (((env () . _.0) ((rec-env () . _.1) ())) _.2)
    (((rec-env () . _.0) ((rec-env () . _.1) ())) _.2)
    ((((env (_.0 _.1) . _.2) ()) _.3)
     (=/= ((_.0 _.3)) ((_.1 _.3))))))

(test-check "10 unification"
  (run 10 (q) (fresh (u^ v^ S o) (unifyo u^ v^ S o) (== `(,u^ ,v^ ,S ,o) q)))
  '(((_.0 _.0 _.1 _.1) (not-pair _.0)) ((_.0 _.1 _.2 #f) (=/= ((_.0 _.1))) (not-pair _.0 _.1))
    ((_.0 (_.1 . _.2) _.3 #f) (=/= ((_.1 var))) (not-pair _.0))
    (((numval . _.0) _.1 _.2 #f) (not-pair _.1))
    (((closure . _.0) _.1 _.2 #f) (not-pair _.1))
    (((_.0 . _.1) _.2 _.3 #f)
     (=/= ((_.0 closure)) ((_.0 numval)) ((_.0 var)))
     (not-pair _.2))
    ((_.0 (var _.1 . _.2) () (((var _.1 . _.2) . _.0)))
     (not-pair _.0))
    ((numval . _.0) (numval . _.0) _.1 _.1)
    (((numval . _.0) (numval . _.1) _.2 #f) (=/= ((_.0 _.1))))
    ((numval . _.0) (closure . _.1) _.2 #f)))

(test-check "100 unifies"
  (length (run 100 (q) (fresh (u^ v^ S o) (unifyo u^ v^ S o) (== `(,u^ ,v^ ,S ,o) q))))
  '100)

(test-check "it runs runs"  
  (run 1 (q) (fresh (a b c d e) (value-ofo `(run (numexp . (1)) (q) (fresh (x) (== q (numexp . (0 0 1))) (== x (numexp . (1 0 1))))) q)))
  '(((((var x 1) . (numval . (1 0 1))) ((var q . 0) . (numval . (0 0 1)))))))

(test-check "letrec"
  (run 1 (q) (value-ofo '(let ((t #t)
                               (f #f))
                           (letrec ((e? (lambda (n)
                                          (if (zero? n)
                                              t
                                              (o? (sub1 n)))))
                                    (o? (lambda (n)
                                          (if (zero? n)
                                              f
                                              (e? (sub1 n))))))
                             (o? (numexp . (0 1 1 1))))) q))
  '(#f))

(test-check "lots of runs"
  (length (run 1000 (q) (fresh (a b) (value-ofo a b) (== `(,a ,b) q))))
  1000)
