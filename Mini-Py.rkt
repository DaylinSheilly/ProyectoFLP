#lang eopl
#|
    Integrantes:
    César Alejandro Grijalba Zúñiga - 202110035
    Johan Sebastian Tombe - 202110051
    Laura Murillas Andrade - 1944153
    Juan Esteban Mazuera - 2043008
    Sheilly Ortega - 2040051
    Link del repositorio: https://github.com/DaylinSheilly/ProyectoFLP.git
|#
#|
    La definición BNF para las expressiones del lenguaje:
    <programa> :=  <expression>
               un-programa (exp)
    <expression>:= <numero>
                numero-lit (num)
                := <identificador>
                id-exp (id)
                := "'"<texto>"'"
                texto-lit (txt)
                := "False"
                falso ()
                := "True"
                verdadero ()
                ("evaluar" <expression> "(" (<expression>)*(,) ")" "finEval")
                app-exp (exp args)
                := "var" "{" <identificador> "=" <expression> "}"*(",") "in" <expression>
                var-def-exp (ids exps cuerpo)
                := "const" "{" <identificador> "=" <expression> "}"*(",") "in" <expression>
                const-def-exp (ids exps cuerpo)
                := "rec" "{" <identificador> "(" "{"<identificador>"}"*(",") ")" "=" <expression> "}"*(",")
                "in" <expression>
                rec-def-exp (funcs ids cuerpof cuerpo)
                := "[" "{" <expression> "}"*(";") "]"
                lista (elems)
                := "[" "{" <expression> "," <expression> "}"*(";") "]"
                tupla (elems1, elems2)
                := "{" "{" <identificador> "=" <expression> "}"+(";") "}"
                registro (ids exps)
                := "begin" "{"<expression>"}"+(";") "fin"
                := "if" <expr-bool> "hacer" "{"<expression>"}" "else" "{"<expression>"}" "fin"
                condicional-exp (test-exp true-exp false-exp)
                := "mientras" <expr-bool> "hacer" "{"<expression>"}" "fin"
                while-exp (test-exp cuerpo)
                := "for" "{"<identificador> "=" <expression> "hasta" <expression>"}" "hacer" "{"<expression>"}" "fin"
                for-exp (id valorInicial limite cuerpo)
                := "set" <identificador> "=" <expression>
                set-exp (id exp)
                := <primitiva> "(" (<expression>)*(",") ")"
                prim-exp (prim exps)
                := <exp-bool>
                bool-exp (exp-bool)
                := primitiva "(" (<expression>)*(",") ")"
                prim-exp (prim exps)
                := <primitiva-hexa> "{" (<hexadecimal>)*"," ")"<expression>")"
                prim-hexa-exp (prim hexa)
                := "precedimiento" "(" (<identificador>)*(",") ")" "haga" <expression> "finProc"
                procedimiento-exp (ids exp)
       exp-bool := <pred-prim> "(" <expression> "," <expression> ")"
                pred-prim-exp (prim exp1 exp2)
                := <oper-bin-bool> "(" <exp-bool> "," <exp-bool> ")"
                oper-bin-bool-exp (prim exp exp1)
                := <oper-un-bool> "(" <exp-bool> ")"
                oper-un-bool-exp (prim exp)
    <pred-prim> := "<" | ">" | "<=" | ">=" | "==" | "<>"
<oper-bin-bool> := "and" | "or"
 <oper-un-bool> := "not"
    <primitiva> := "+" (primitiva-suma)
                := "~" (primitiva-resta)
                := "*" (primitiva-multi)
                := "%" (primitiva-mod)
                := "/" (primitiva-div)
                := "add1" (primitiva-add1)
                := "sub1" (primitiva-sub1)
                := "longitud" (primitiva-longitud)
                := "concat" (primitiva-concat)
                := "lista?" (primitiva-lista?)
                := "lista" (primitiva-crear-lista)
                := "append" (primitiva-append)
                := "ref-list" (primitiva-ref-lista)
                := "set-list" (primitiva-set-lista)
                := "cabeza-lista" (primitiva-cabeza-lista)
                := "cola-lista" (primitiva-cola-listaa)
                := "tupla?" (primitiva-tupla?)
                := "crear-tupla" (primitiva-crear-tupla)
                := "ref-tupla" (primitiva-ref-tupla)
                := "cabeza-tupla" (primitiva-cabeza-tupla)
                := "cola-tupla" (primitiva-cola-tupla)
                := "vacio" (primitiva-vacio)
                := "vacio?" (primitiva-vacio?)
                := "registro?" (primitiva-registro?)
                := "crear-registro" (primitiva-crear-registro)
                := "ref-registro" (primitiva-ref-registro)
                := "set-registro" (primitiva-set-registro)
                := "suma" (suma-hexa)
                := "resta" (resta-hexa)
                := "multi" (multi-hexa)
                := "*hadd1" (add1-hexa)
                := "*hsub1" (sub1-hexa)
|#

;Especificación Léxica

(define scanner-spec-simple-interpreter
'((white-sp (whitespace) skip)
  (comment ("#"(arbno (not #\newline))) skip)
  (caracter ("/" letter "/") string)
  (texto ("'" (arbno (or letter digit whitespace "\"" "-" ":" "." "," ";" "!" "¡" "¿" "?" "(" ")")) "'") string)
  (identificador ( letter (arbno (or letter digit))) symbol)
  ;enteros positivos y negativos
  (numero (digit (arbno digit)) number)
  (numero ("-" digit (arbno digit)) number)
  ;flotantes
  (numero (digit (arbno digit) "." digit (arbno digit)) number)
  (numero ("-" digit (arbno digit) "." digit (arbno digit)) number)
  ;Octales
  (octal("*o(" (or "0" "1" "2" "3" "4" "5" "6" "7")
        (arbno (or "0" "1" "2" "3" "4" "5" "6" "7"))) string)
  ;Hecadecimales
  (hexadecimal("*h" (or "0" "1" "2" "3" "4" "5" "6" "7" "8" "9" "a" "b" "c" "d" "e" "f")
              (arbno(or "0" "1" "2" "3" "4" "5" "6" "7" "8" "9" "a" "b" "c" "d" "e" "f"))) string)
 )
)

;Especificación Sintáctica (gramática)

(define grammar-simple-interpreter
  '(
    ;Programa
    (programa ((arbno class-decl) expression) un-programa)

    ;declracion de la clase
    (class-decl
      ("class" identificador
        "extends" identificador
         (arbno "field" identificador)
         (arbno method-decl)
         )
      a-class-decl)

    ;declaracion del metodo
    (method-decl
      ("method" identificador
        "("  (separated-list identificador ",") ")" ; method ids
        expression
        )
      a-method-decl)

    ;expresiones para los objetos
    (expression ("new" identificador "(" (separated-list expression ",") ")") new-object-exp)

    (expression ("send" expression identificador "(" (separated-list expression ",") ")") method-app-exp)

    (expression ("super" identificador    "("  (separated-list expression ",") ")") super-call-exp)

    ;datos
    (expression (numero) numero-lit)
    (expression (identificador) id-exp) ;(scan&parse "id")
    (expression (caracter) char-exp)
    (expression (texto) texto-lit) ;(scan&parse "'escribir usando comillas simples ('hola')'")
    (expression ("False") falso) ;(scan&parse "False")
    (expression ("True") verdadero) ;(scan&parse "True")

    (expression ("evaluar"  expression "("(separated-list expression ",") ")" "finEval") app-exp)

    ;definiciones
    (expression ("var" "{" (arbno identificador "=" expression ";") "}" "in" expression) var-exp)
    (expression ("const" "{" (arbno identificador "=" expression ";") "}" "in" expression) const-exp)
    (expression ("rec" (arbno identificador "(" (separated-list identificador ",") ")" "=" expression )  "in" expression) rec-exp)

    ;constructores de datos predefinidos
    (expression ("[" (separated-list expression ",") "]") lista)
    ;(scan&parse "[1,2,3]")
    (expression ("tupla" "[" (separated-list expression ",") "]") tupla)
    ;(scan&parse "tupla[1,2,3]")
    (expression ("{" "{"identificador "=" expression "}"";" (arbno "{"identificador "=" expression "}"";") "}") registro)
    ;(scan&parse "{{a=1};{b=2};{c=3};}")

    ;estructuras de control
    (expression ("begin" "{" expression ";" (arbno expression ";") "}" "fin") begin-exp)
    (expression ("if" exp-bool "hacer" "{" expression "}" "else" "{" expression "}" "fin") condicional-exp)
    (expression ("declarar" "(" (separated-list identificador "=" expression ";") ")" "hacer" "{" expression "}") variableLocal-exp)
    (expression ("mientras" exp-bool "hacer" "{" expression "}" "fin" ) while-exp)
    (expression ("for" "(" identificador "=" expression "hasta" expression ")" "hacer" "{" expression "}" "fin") for-exp)

    (expression ("set" identificador "=" expression) set-exp)

    (expression (primitiva "(" (separated-list expression ",") ")")  prim-exp)

    (expression (exp-bool) bool-exp)

    ;expresiones octales y hexadecimales
    (expression (octal) octal-exp)
    (expression (hexadecimal) hexa-exp)
    (expression (primitiva-hexa "{" (separated-list hexadecimal ",") "}") prim-hexa-exp)

    ;procedimientos
    (expression ("procedimiento" "(" (separated-list identificador ",") ")" "haga" expression "finProc" ) procedimiento-exp)

    ;expresiones booleanas
    (exp-bool (pred-prim "("expression "," expression")") pred-prim-exp)
    (exp-bool (oper-bin-bool "(" exp-bool "," exp-bool ")") oper-bin-bool-exp)
    (exp-bool (oper-un-bool "(" exp-bool ")") oper-un-bool-exp)

    (pred-prim ("<") menorQue)
    (pred-prim (">") mayorQue)
    (pred-prim ("<=") menorOigualQue)
    (pred-prim (">=") mayorOigualQue)
    (pred-prim ("==") igual)
    (pred-prim ("<>") diferente)

    (oper-bin-bool ("and") boolAnd)
    (oper-bin-bool ("or") boolOr)

    (oper-un-bool ("not") boolNot)

    ;Primitivas

    (primitiva ("imprimir") primitiva-print)

    ;;Primitiva numeros
    (primitiva ("+") primitiva-suma)
    (primitiva ("~") primitiva-resta)
    (primitiva ("*") primitiva-multi)
    (primitiva ("/") primitiva-div)
    (primitiva ("%") primitiva-mod)
    (primitiva ("add1") primitiva-add1)
    (primitiva ("sub1") primitiva-sub1)

    ;Primitivas sobre cadenas
    (primitiva ("concat") primitiva-concat)
    (primitiva ("longitud")  primitiva-longitud)

    ;primitivas sobre listas
    (primitiva ("lista?") primitiva-lista?)
    (primitiva ("lista") primitiva-crear-lista)
    (primitiva ("append") primitiva-append)
    (primitiva ("ref-list") primitiva-ref-lista)
    (primitiva ("set-list") primitiva-set-lista)
    (primitiva ("cabeza-lista") primitiva-cabeza-lista)
    (primitiva ("cola-lista") primitiva-cola-listaa)

    ;primiivas sobre tuplas
    (primitiva ("tupla?") primitiva-tupla?)
    (primitiva ("crear-tupla") primitiva-crear-tupla)
    (primitiva ("ref-tupla") primitiva-ref-tupla)
    (primitiva ("cabeza-tupla") primitiva-cabeza-tupla)
    (primitiva ("cola-tupla") primitiva-cola-tupla)

    ;Primitivas sobre listas y tuplas
    (primitiva ("vacio") primitiva-vacio)
    (primitiva ("vacio?") primitiva-vacio?)

    ;primitivas sobre registros
    (primitiva ("registro?") primitiva-registro?)
    (primitiva ("crear-registro") primitiva-crear-registro)
    (primitiva ("ref-registro") primitiva-ref-registro)
    (primitiva ("set-registro") primitiva-set-registro)

    (primitiva-hexa ("suma") suma-hexa)
    (primitiva-hexa ("resta") resta-hexa)
    (primitiva-hexa ("multi") multi-hexa)
    (primitiva-hexa ("*hadd1") add1-hexa)
    (primitiva-hexa ("*hsub1") sub1-hexa)
  )
)

;*******************************************************************************************
;Tipos de datos para la sintaxis abstracta de la gramática construidos automáticamente:

(sllgen:make-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)

(define show-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)
  )
)

;*******************************************************************************************
;Parser, Scanner, Interfaz

;El FrontEnd (Análisis léxico (scanner) y sintáctico (parser) integrados)

(define scan&parse
  (sllgen:make-string-parser scanner-spec-simple-interpreter grammar-simple-interpreter)
)

;El Analizador Léxico (Scanner)

(define just-scan
  (sllgen:make-string-scanner scanner-spec-simple-interpreter grammar-simple-interpreter)
)

;El Interpretador (FrontEnd + Evaluación + señal para lectura )

(define interpretador
  (sllgen:make-rep-loop  "--❤ "
    (lambda (pgm) (eval-programa  pgm))
    (sllgen:make-stream-parser
      scanner-spec-simple-interpreter
      grammar-simple-interpreter)
   )
 )

;*******************************************************************************************
;El Interprete

;eval-programa: <programa> -> expression
; función que evalúa un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)

(define eval-programa
  (lambda (pgm)
    (cases programa pgm
      (un-programa (c-decls exp)
                 (elaborate-class-decls! c-decls)
                 (eval-expression exp (init-env))
      )
    )
  )
)

; Ambiente inicial
(define init-env
  (lambda ()
    (extend-env
      '(a b c d e)
      (list 1 2 3 "Hola" "FLP")
      (empty-env)
    )
  )
)


;eval-expression: <expression> <enviroment> ->
; evalua la expresión en el ambiente de entrada, para cada caso (numero-lit,var-exp,texto-lit, condicional-exp, variableLocal-exp
;procedimiento-exp, app-exp, letrec, primapp-bin-exp, primapp-un-exp) devuelve algo diferente dependiendo del caso de la expresión.
(define eval-expression
  (lambda (exp env)
    (cases expression exp
      (numero-lit (numero) numero)
      (id-exp (id)(apply-env env id))
      (char-exp (char) (recortar-string char env))
      (texto-lit (txt) (recortar-string txt env))
      (verdadero () #t)
      (falso () #f)
      (prim-exp (prim exp)
                (cases primitiva prim
                  (primitiva-ref-registro () (let ((ids (vector->list (car (eval-expression (car exp) env))))
                                                  (vals (vector->list (cadr (eval-expression (car exp) env)))))
                                               (eval-expression (cadr exp) (extend-env ids vals env))))

                (primitiva-set-registro () (let ((ids (vector->list (car (eval-expression (car exp) env))))
                                                (vals (vector->list (cadr (eval-expression (car exp) env))))
                                                (dic (eval-expression (car exp)   env))
                                                (id (cases expression (cadr exp) (id-exp (id) id) (else #f)))
                                                (val (eval-expression (caddr exp) env)))
                                             (begin(let ((pos (rib-find-position id ids)))
                                                        (if (number? pos)
                                                        (vector-set! (cadr dic) pos val)
                                                        "error"))1)))
                  (else(let ((args (eval-prim-exp-rands exp env)))
                           (apply-primitiva prim args env)))))

      (lista (exp) (let ((args (eval-prim-exp-rands exp env)))
                       (if (not (null? args))
                           (apply-lista (list->vector args))
                           '())))

      (tupla (exp) (let ((args (eval-prim-exp-rands exp env)))
                     (if (not (null? args))
                         (list (car args) (cadr args))'())))

      (registro (id exp list-id list-exp) (let ((args (eval-prim-exp-rands list-exp env))
                                                (arg (eval-expression exp env)))
                                          (apply-registro id arg list-id args )))

      (condicional-exp (exp-bool true-exp false-exp)
                       (if (eval-exp-bool exp-bool env)
                           (eval-expression true-exp env)
                           (eval-expression false-exp env)))

      (rec-exp (proc-names idss bodies letrec-body)
                  (eval-expression letrec-body
                                   (extend-env-recursively proc-names idss bodies env)))
      (app-exp (exp exps)
               (let ((proc (eval-expression exp env))
                     (args (eval-rands exps env)))
                 (if (procval? proc)
                     (apply-procedure proc args)
                     (eopl:error 'eval-expression "Attempt to apply non-procedure ~s" proc))))

      (procedimiento-exp (ids cuerpo) (cerradura ids cuerpo env))

      (var-exp (ids exps cuerpo)
               (let ((args (eval-let-exp-rands exps env)))
                    (eval-expression cuerpo (extend-env ids args env))))

      (const-exp (ids rands body)
                 (begin
                   (eval-set rands)
                   (cases expression body
                     (set-exp (id exp) (eopl:error 'evaluar-expression
                                              "No es posible modificar una constante"))
                     (else (let ((args (eval-let-exp-rands rands env)))
                             (eval-expression body (extend-env ids args env)))))))

      (set-exp (id rhs-exp)
               (begin
                 (setref!
                  (apply-env-ref env id)
                  (eval-expression rhs-exp env))1))

      (begin-exp (exp exps)
                 (let loop ((acc (eval-expression exp env)) (exps exps))
                    (if (null? exps)
                        acc
                        (loop (eval-expression (car exps) env) (cdr exps)))))

      (while-exp (exp-bool exp)
                  (let   loop ((i 0))

                   (when (eval-exp-bool exp-bool env)
                      (eval-expression exp env)
                      (loop (+ 1 i)))))

      (variableLocal-exp (ids exps cuerpo)
               (let ((args (eval-rands exps env)))
                 (eval-expression cuerpo (extend-env ids args env))))

      (for-exp ( exp desde hasta cuerpo)
         (let
             ((de (eval-expression desde env))
                   (to (eval-expression hasta env)))
            (let   loop ((i de))
                   (when (< i to)
                      (eval-expression cuerpo (extend-env (list exp) (list i) env))
                      (loop (+ 1 i))))))

     (bool-exp (exp) (eval-exp-bool exp env))

     ;hexadecimales
      (octal-exp (octal) octal)
      (hexa-exp (hexa) hexa)
      (prim-hexa-exp (prim hexa) (cases primitiva-hexa prim
                                 (suma-hexa () (number->string (+ (string->number (string-append "#x"(substring (car hexa) 2)) 16)
                                                                  (string->number (string-append "#x"(substring (cadr hexa) 2)) 16)) 16))
                                 (resta-hexa () (number->string (- (string->number (string-append "#x"(substring (car hexa) 2)) 16)
                                                                  (string->number (string-append "#x"(substring (cadr hexa) 2)) 16)) 16))
                                 (multi-hexa () (number->string (* (string->number (string-append "#x"(substring (car hexa) 2)) 16)
                                                                  (string->number (string-append "#x"(substring (cadr hexa) 2)) 16)) 16))
                                 (add1-hexa () (number->string (+ (string->number (string-append "#x"(substring (car hexa) 2)) 16) 1) 16))
                                 (sub1-hexa () (number->string (- (string->number (string-append "#x"(substring (car hexa) 2)) 16) 1) 16))
                                 )
      )

      ;objetos
     (new-object-exp (class-name rands)
        (let ((args (eval-rands rands env))
              (obj (new-object class-name)))
          (find-method-and-apply
            '@initialize class-name obj args)
          obj)
      )

      (method-app-exp (obj-exp method-name rands)
        (let ((args (eval-rands rands env))
              (obj (eval-expression obj-exp env)))
          (find-method-and-apply
            method-name (object->class-name obj) obj args)))

      (super-call-exp (method-name rands)
        (let ((args (eval-rands rands env))
              (obj (apply-env env '@self)))
          (find-method-and-apply
            method-name (apply-env env '%super) obj args)))
      (else #t))))
;funciones auxiliares

;evalúa si hay set en los argumentos de los const
(define eval-set
  (lambda (rands)
    (cond
      [(null? rands) #true]
      [else
       (cases expression (car rands)
                     (set-exp (id exp) (eopl:error 'evaluar-expression
                                 "No es posible modificar una constante" ))
                     (else (eval-set (cdr rands))))])))

;asi se crea una lista
(define apply-lista
  (lambda (exp)
     exp))

;asi se crea un registro
(define apply-registro
  (lambda (id arg list-id args)
    (list (list->vector (cons id list-id)) (list->vector (cons arg args)))))

; funciones auxiliares para aplicar eval-expression a cada elemento de una
; lista de operandos (expressiones)

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

(define eval-rand
  (lambda (rand env)
    (cases expression rand
      (lista (exp)
             (indirect-target
                (let ((ref (apply-env-ref env exp)))
                  (cases target (primitive-deref ref)
                    (direct-target (expval) ref)
                    (indirect-target (ref1) ref1)))))
      (else
       (direct-target (eval-expression rand env))))))

(define eval-prim-exp-rands
  (lambda (rands env)
    (map (lambda (x) (eval-expression x env)) rands)))

(define eval-let-exp-rands
  (lambda (rands env)
    (map (lambda (x) (eval-let-exp-rand x env))
         rands)))

(define eval-let-exp-rand
  (lambda (rand env)
    (direct-target (eval-expression rand env))))

;evalua las primitivas
(define apply-primitiva
  (lambda (prim exps env)
    (cases primitiva prim
      (primitiva-print () (display (car exps) ) )

      ;sobre numeros
      (primitiva-suma () (+ (car exps) (cadr exps)))
      (primitiva-resta () (- (car exps) (cadr exps)))
      (primitiva-div () (/ (car exps) (cadr exps)))
      (primitiva-multi () (* (car exps) (cadr exps)))
      (primitiva-mod () (modulo (car exps) (cadr exps)))
      (primitiva-add1 () (+ (car exps) 1))
      (primitiva-sub1 () (- (car exps) 1))

      ;sobre cadenas
      (primitiva-concat () (string-append (recortar-string (car exps) env) (recortar-string (cadr exps) env)))
      (primitiva-longitud () (string-length (car exps)))

      ;sobre listas y tuplas
      (primitiva-vacio () '())
      (primitiva-vacio? () (if (null? (car exps)) #t #f))

      ;sobre listas
      (primitiva-lista? () (if (vector? (car exps)) #t #f ))
      (primitiva-append () (list->vector (append (vector->list (car exps)) (vector->list (cadr exps)))))
      (primitiva-crear-lista () (list->vector (cons (car exps) (vector->list (cadr exps)))))
      (primitiva-ref-lista () (vector-ref (car exps) (cadr exps)))
      (primitiva-set-lista ()
                          (begin
                            (vector-set! (car exps) (cadr exps) (caddr exps)) 1)
      )
      (primitiva-cabeza-lista () (vector-ref (car exps) 0))
      (primitiva-cola-listaa () (begin
                                (define a (make-vector (- (vector-length (car exps))1)))
                                 (let   loop ((i 0))
                                   (when (< i (- (vector-length (car exps)) 1))
                                     (vector-set! a i (vector-ref (car exps) (+ i 1)))
                                     (loop (+ 1 i)))) a))

      ;sobre tuplas
      (primitiva-tupla? () (if (and (list? (car exps) ) (= (length (car exps)) 2) ) #t #f ))
      (primitiva-crear-tupla () (list (car exps) (cadr exps)))
      (primitiva-ref-tupla () (list-ref (car exps) (cadr exps)))
      (primitiva-cabeza-tupla () (car (car exps)))
      (primitiva-cola-tupla () (cdr (car exps)))

      ;sobre registros
      (primitiva-registro? ()
                           (if (list? (car exps))
                             (let(
                                 (len (length (car exps)))
                                 (ids (caar exps))
                                 (vals (cadr (car exps)))
                               )
                               (if (and (and (= len 2) (vector? ids)) (vector? vals))
                                 #t
                                 #f
                               )
                              )
                           #f)
                          )
      (primitiva-crear-registro ()
                                (let
                                    ( (id (vector-ref (caar exps) 0))
                                      (list-id (vector->list (caadr exps)) )
                                      (arg (vector-ref (cadr (car exps)) 0) )
                                      (args (vector->list (cadr (cadr exps))) )
                                     )
                                   (apply-registro id arg list-id args )))
      (primitiva-ref-registro () #f ) ;Esta primitiva está implementada en el eval-expression
      (primitiva-set-registro () #t );Esta primitiva está implementada en el eval-expression
    )
  )
)

;medir-texto: <string> -> <number>
(define medir-texto
  (lambda (exp env)
    (cases expression exp
      (texto-lit (txt) (-(string-length (eval-expression exp env))2))
      (id-exp (id) (string-length (eval-expression exp env)))
      (else (0))
    )
  )
)

;recortar-string: <string> -> <string>
(define recortar-string
  (lambda (exp env)
    (substring exp 1 (- (string-length exp) 1)
    )
  )
)

;booleanos

;función auxiliar para evaluar expresiones booleanas
(define eval-exp-bool
  (lambda (exp env)
    (cases exp-bool exp
      (pred-prim-exp (pred-prim exp1 exp2) (apply-pred-prim pred-prim exp1 exp2 env))
      (oper-bin-bool-exp (pred-bin-prim exp1 exp2) (apply-oper-bin-bool pred-bin-prim (eval-exp-bool exp1 env) (eval-exp-bool exp2 env) env))
      (oper-un-bool-exp (pred-un-prim exp) (apply-oper-un-bool pred-un-prim (eval-exp-bool exp env) env)))))

;funcion auxiliar para evaluar una expresion pred-prim
(define apply-pred-prim
  (lambda (pred-prim-expr exp1 exp2 env)
    (cases pred-prim pred-prim-expr
      (menorQue () (< (eval-expression exp1 env) (eval-expression exp2 env)))
      (mayorQue () (> (eval-expression exp1 env) (eval-expression exp2 env)))
      (menorOigualQue () (<= (eval-expression exp1 env) (eval-expression exp2 env)))
      (mayorOigualQue () (>= (eval-expression exp1 env) (eval-expression exp2 env)))
      (igual () (= (eval-expression exp1 env) (eval-expression exp2 env)))
      (diferente () (not (= (eval-expression exp1 env) (eval-expression exp2 env)))))))

;funcion auxiliar para evaluar una expresion oper-bin-bool
(define apply-oper-bin-bool
  (lambda (oper-bin-bool-exp exp1 exp2 env)
    (cases oper-bin-bool oper-bin-bool-exp
      (boolAnd () (and exp1 exp2))
      (boolOr () (or exp1 exp2)))))

;funcion auxiliar para evaluar una expresion oper-un-bool
(define apply-oper-un-bool
  (lambda (oper-un-bool-exp expr-bool env)
    (cases oper-un-bool oper-un-bool-exp
      (boolNot () (not expr-bool)))))

;Procedimientos

;se crea el tipo de dato procval
(define-datatype procval procval?
  (cerradura
   (lista-ID (list-of symbol?))
   (exp expression?)
   (amb environment?)))

;apply-procedure: <process> <arguments> -> <>
;proposito: Evalua el cuerpo de un procedimientos en el ambiente extendido correspondiente

(define apply-procedure
  (lambda (proc args)
    (cases procval proc
      (cerradura (ids body env)
               (eval-expression body (extend-env ids args env))))))

;*******************************************************************************************
;Ambientes

;definición del tipo de dato ambiente
(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vec vector?)
   (env environment?)))

(define scheme-value? (lambda (v) #t))

;empty-env:      -> enviroment
;función que crea un ambiente vacío
(define empty-env
  (lambda ()
    (empty-env-record)))       ;llamado al constructor de ambiente vacío

;extend-env: <list-of symbols> <list-of numbers> enviroment -> enviroment
;función que crea un ambiente extendido
(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (list->vector vals) env)))

;extend-env-recursively: <list-of symbols> <list-of <list-of symbols>> <list-of expressions> environment -> environment
;función que crea un ambiente extendido para procedimientos recursivos
(define extend-env-recursively
  (lambda (proc-names idss bodies old-env)
    (let ((len (length proc-names)))
      (let ((vec (make-vector len)))
        (let ((env (extended-env-record proc-names vec old-env)))
          (for-each
            (lambda (pos ids body)
              (vector-set! vec pos (direct-target (cerradura ids body env))))
            (iota len) idss bodies)
          env)))))

;iota: number -> list
;función que retorna una lista de los números desde 0 hasta end
(define iota
  (lambda (end)
    (let
        loop ((next 0))
        (if (>= next end)
            '()
            (cons next (loop (+ 1 next)))
        )

     )
   )
 )

;función que busca un símbolo en un ambiente
(define apply-env
  (lambda (env sym)
      (deref (apply-env-ref env sym))))

(define apply-env-ref
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
                        (eopl:error 'apply-env-ref "No binding for ~s" sym))
      (extended-env-record (syms vals env)
                           (let ((pos (rib-find-position sym syms)))
                             (if (number? pos)
                                 (a-ref pos vals)
                                 (apply-env-ref env sym)))))))

;**************************************************************************************
;Definición tipos de datos referencia y blanco

(define-datatype target target?
  (direct-target (expval expval?))
  (indirect-target (ref ref-to-direct-target?)))

(define-datatype reference reference?
  (a-ref (position integer?)
         (vec vector?)))

;*******************************************************************************************
;Blancos y Referencias
(define expval?
  (lambda (x)
    (or (or (or (number? x) (procval? x) ) list? x) vector? x)
  )
)

(define ref-to-direct-target?
  (lambda (x)
    (and (reference? x)
         (cases reference x
           (a-ref (pos vec)
                  (cases target (vector-ref vec pos)
                    (direct-target (v) #t)
                    (indirect-target (v) #f)))))))

(define deref
  (lambda (ref)
    (if (target? (primitive-deref ref))
    (cases target (primitive-deref ref)
      (direct-target (expval) expval)
      (indirect-target (ref1)
                       (cases target (primitive-deref ref1)
                         (direct-target (expval) expval)
                         (indirect-target (p)
                                          (eopl:error 'deref
                                                      "Illegal reference: ~s" ref1)))))
    (primitive-deref ref))))

(define primitive-deref
  (lambda (ref)
    (cases reference ref
      (a-ref (pos vec)
             (vector-ref vec pos)))))

(define setref!
  (lambda (ref expval)
    (if (target? (primitive-deref ref))
    (let

        ((ref (cases target (primitive-deref ref)
                (direct-target (expval1) ref)
                (indirect-target (ref1) ref1))))
      (primitive-setref! ref (direct-target expval)))
    (primitive-setref! ref expval))))

(define primitive-setref!
  (lambda (ref val)
    (cases reference ref
      (a-ref (pos vec)
             (vector-set! vec pos val)))))

(define extend-env-refs
  (lambda (syms vec env)
    (extended-env-record syms vec env)))

;****************************************************************************************
; funciones auxiliares para encontrar la posición de un símbolo
; en la lista de símbolos de un ambiente

(define rib-find-position
  (lambda (sym los)
    (list-find-position sym los)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))

;****************************************************************************************
;implementacion de Objetos

;declaraciones

(define class-decl->class-name
  (lambda (c-decl)
    (cases class-decl c-decl
      (a-class-decl (class-name super-name field-ids m-decls)
        class-name))))

(define class-decl->super-name
  (lambda (c-decl)
    (cases class-decl c-decl
      (a-class-decl (class-name super-name field-ids m-decls)
        super-name))))

(define class-decl->field-ids
  (lambda (c-decl)
    (cases class-decl c-decl
      (a-class-decl (class-name super-name field-ids m-decls)
        field-ids))))

(define class-decl->method-decls
  (lambda (c-decl)
    (cases class-decl c-decl
      (a-class-decl (class-name super-name field-ids m-decls)
        m-decls))))

(define method-decl->method-name
  (lambda (md)
    (cases method-decl md
      (a-method-decl (method-name ids body) method-name))))

(define method-decl->ids
  (lambda (md)
    (cases method-decl md
      (a-method-decl (method-name ids body) ids))))

(define method-decl->body
  (lambda (md)
    (cases method-decl md
      (a-method-decl (method-name ids body) body))))

(define method-decls->method-names
  (lambda (mds)
    (map method-decl->method-name mds)))

;**********************************************************************************
;;evaluar 

(define aux
   (lambda (x)
     x))

(define-datatype part part? 
  (a-part
    (class-name symbol?)
    (fields vector?)))

(define new-object
  (lambda (class-name)
    (if (eqv? class-name '@object)
      '()
      (let ((c-decl (lookup-class class-name)))
        (cons
          (make-first-part c-decl)
          (new-object (class-decl->super-name c-decl)))))))

(define make-first-part
  (lambda (c-decl)
    (a-part
      (class-decl->class-name c-decl)
      (make-vector (length (class-decl->field-ids c-decl))))))

;;;;;;;; methods ;;;;;;;;

;; methods are represented by their declarations.  They are closed
;; over their fields at application time, by apply-method.

(define find-method-and-apply
  (lambda (m-name host-name self args)
    (if (eqv? host-name '@object)
      (eopl:error 'find-method-and-apply
        "No method for name ~s" m-name)
      
      (let ((m-decl (lookup-method-decl m-name
                      (class-name->method-decls host-name))))
        (if (method-decl? m-decl)
          (apply-method m-decl host-name self args)
          (find-method-and-apply m-name (class-name->super-name host-name) self args))))))

(define view-object-as
  (lambda (parts class-name)
    (if (eqv? (part->class-name (car parts)) class-name)
      parts
      (view-object-as (cdr parts) class-name))))

(define apply-method
  (lambda (m-decl host-name self args)
    (let ((ids (method-decl->ids m-decl))
          (body (method-decl->body m-decl))
          (super-name (class-name->super-name host-name)))
      (eval-expression body
        (extend-env
          (cons '%super (cons '@self ids))
          (cons super-name (cons self args))
          (build-field-env 
            (view-object-as self host-name)))))))

(define build-field-env
  (lambda (parts)
    (if (null? parts)
      (empty-env)
      (extend-env-refs
        (part->field-ids (car parts))
        (part->fields    (car parts))
        (build-field-env (cdr parts))))))

;;;;;;;; method environments ;;;;;;;;

; find a method in a list of method-decls, else return #f

(define lookup-method-decl 
  (lambda (m-name m-decls)
    (cond
      ((null? m-decls) #f)
      ((eqv? m-name (method-decl->method-name (car m-decls)))
       (car m-decls))
      (else (lookup-method-decl m-name (cdr m-decls))))))

;;;;;;;; class environments ;;;;;;;;

;; we'll just use the list of class-decls.

(define the-class-env '())

(define elaborate-class-decls!
  (lambda (c-decls)
    (set! the-class-env c-decls)))

(define lookup-class
  (lambda (name)
    (let loop ((env the-class-env))
      (cond
        ((null? env)
         (eopl:error 'lookup-class
           "Unknown class ~s" name))
        ((eqv? (class-decl->class-name (car env)) name) (car env))
        (else (loop (cdr env)))))))

;;;;;;;; selectors of all sorts ;;;;;;;;

(define part->class-name
  (lambda (prt)
    (cases part prt
      (a-part (class-name fields)
        class-name))))

(define part->fields
  (lambda (prt)
    (cases part prt
      (a-part (class-name fields)
        fields))))

(define part->field-ids
  (lambda (part)
    (class-decl->field-ids (part->class-decl part))))

(define part->class-decl
  (lambda (part)
    (lookup-class (part->class-name part))))

(define part->method-decls
  (lambda (part)
    (class-decl->method-decls (part->class-decl part))))

(define part->super-name
  (lambda (part)
    (class-decl->super-name (part->class-decl part))))

(define class-name->method-decls
  (lambda (class-name)
    (class-decl->method-decls (lookup-class class-name))))

(define class-name->super-name
  (lambda (class-name)
    (class-decl->super-name (lookup-class class-name))))

(define object->class-name
  (lambda (parts)
    (part->class-name (car parts))))

#|
;ejemplos

;datos
;enteros positivos y negativos: (scan&parse "123") | (scan&parse "123")
;flotantes: (scan&parse "-1.23") | (scan&parse "-1.23")
;octales:
;hexadecimales:
;identificador: (scan&parse "id")
;texto: (scan&parse "'escribir usando comillas simples hola'")
;falso: (scan&parse "False")
;verdadero: (scan&parse "True")

;constructores de datos predefinidos
;lista: (scan&parse "[1,2,3]")
;tupla: (scan&parse "tupla[1,2,3]")
;registro: (scan&parse "{{a=1};{b=2};{c=3};}")

;expresiones booleanas
;pred-prim: <(1,2)
;oper-bin-bool: and(<(1,2),<(3,19))
;oper-un-bool: not(>(1,2))

;primitivas sobre listas
;(scan&parse "[1,2,3]")
;primitiva-lista?: lista?([1,2,3])"
;primitiva-append: append([1,2],[3])
;primitiva-ref-lista: ref-list([1,2,3], 4)
;primitiva-set-lista: set-list([1,2,3], 9, 3)
;primitiva-cabeza-lista: cabeza-lista([1,2,3])
;primitiva-cola-lista: cola-lista([1,2,3])

;primitivas sobre tuplas
;(scan&parse "tupla[1,2,3]")
;primitiva-tupla?: tupla?(tupla[1,2])
;primitiva-crear-tupla: crear-tupla(1,2)
;primitiva-ref-tupla: ref-tupla( tupla[1,2], 1)
;primitiva-cabeza-tupla: cabeza-tupla(tupla[1,2])
;primitiva-cola-tupla: cola-tupla(tupla[1,2])
;primitiva-vacio?: vacio?(tupla[])
;primitiva-vacio: vacio()

;primitivas sobre registros
;primitiva-registro?: registro?({{b=1}; {a=2};})
;primitiva-crear-registro: crear-registro({{a=1};},{ {b=2};{c=3};})
;primitiva-ref-registro: ref-registro({{a=1};{c=2};},a)
;primitiva-set-registro: set-registro({{a=1};{c=2};},a,3)

;Ejemplo Objetos
(scan&parse "class c1 extends object
               field x
               field y
               method initialize()
                 begin{
                  set x = 1;
                  set y = 2;
                 }fin
              method m1() x
              method m2() y
            var
            { o1 = new c1() ; }
            in
            send o1 m1()
")
|#