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
    La definición BNF para las expresiones del lenguaje:
    <programa> :=  <expression> 
               un-programa (exp)
    <expression>:= <numero>
                numero-lit (num)
                := "'"<cadena>"'"
                char-lit (char)
                := <bool>
                bool-lit (bool)
                := <identificador>
                id-exp (id)
                := <lista>
                list-expr (list)
                := <tupla>
                tupla-exp (tupla)
                := <registro>
                registro-exp (registro)
                := <expr-bool>
                bool-exp (boolean-exp)
                := "("<expression> <primitiva-para-numeros> <expression>")"
                primapp-int-exp (exp1 prim-number exp2)
                := <primitiva-sobre-cadenas> "("<expression>")"
                primapp-str-exp (prim-str exp)
                := "var" "{" <identificador> "=" <expression> "}"*(",") "in" <expression>
                var-def-exp (ids exps cuerpo)
                := "const" "{" <identificador> "=" <expression> "}"*(",") "in" <expression>
                const-def-exp (ids exps cuerpo)
                := "rec" "{" <identificador> "(" "{"<identificador>"}"*(",") ")" "=" <expression> "}"*(",")
                "in" <expresion>
                rec-def-exp (funcs ids cuerpof cuerpo)
                := "begin" "{"<expression>"}"+(";") "end"
                := "if" <expr-bool> "then" <expression> "[" "else"   <expression> "]" "end"
                condicional-exp(test-exp true-exp false-exp)
                := "while" <expr-bool> "do"
                := "for" <identificador> "=" <expression> "(" "to" | "downto" ")" <expression> "do"
                := set <identificador> = <expresion>
;;              set-exp (idSet expSet)
                := "done"
    <identificador> := <cadena> | "{" <cadena> | <numero> "}"
                    id (char num)
    <primitiva-para-numeros> :=  "+" (primitiva-suma)
                             :=  "-" (primitiva-resta)
                             :=  "*" (primitiva-multi)
                             :=  "%" (primitiva-mod)
                             :=  "/" (primitiva-div)
                             :=  "add1" (primitiva-add1)
                             :=  "sub1" (primitiva-sub1)
    <primitiva-sobre-cadenas> :=  "longitud" (primitiva-longitud)
                              :=  "concat" (primitiva-concat)
    <lista> := "[" "{" <expression> "}"*(";") "]"
            list-exp (elems)
    <tupla> := "[" "{" <expression> "," <expression> "}"*(";") "]"
            tup-exp (elems1, elems2)
    <registro> := "{" "{" <identificador> "=" <expression> "}"+(";") "}"
            reg-exp (ids exps)
    <expr-bool> := <pred-prim> "(" <expression> <expression> ")"*(",")
                := <oper-bin-bool> "("<expr-bool > <expr-bool>")"*(",")
                := <bool>
                := <oper-un-bool>"("<expr-bool>")"
    <pred-prim> := "<" | ">" | "<=" | ">=" | "==" | "<>"
    <oper-bin-bool> := "and" | "or"
    <oper-un-bool> := "not"
    <primitiva-sobre-listas> := "(" "vacio?" <lista> ")"
                             := "(" "vacio" <lista> ")"
                             := "(" "lista?" <lista> ")"
                             := "(" "crear-lista" <lista> ")"
                             := "(" "cabeza" <lista> ")"
                             := "(" "cola" <lista> ")"
                             := "(" <lista> "append" <lista> ")"
                             := "ref-list" ;???
                             := "set-list" ;???
    <primitiva-sobre-tuplas> := "(" "vacio?" <tupla> ")"
                             := "(" "vacio" <tupla> ")"
                             := "(" "tupla?" <tupla> ")"
                             := "(" "crear-tupla" <tupla> ")"
                             := "(" "cabeza" <tupla> ")"
                             := "(" "cola" <tupla> ")"
                             := "ref-tupla" ;???
                             
    <primitiva-sobre-registro> := "(" "registro?" <tupla> ")"
                            := "(" "crear-registro" <tupla> ")"
                            := "ref-registro" ;???
                            := "set-registro" ;???
|#

;Especificación Léxica

(define scanner-spec-simple-interpreter
'((white-sp (whitespace) skip)
  (comment ("#"(arbno (not #\newline))) skip)
  (texto ("'" (arbno (or letter digit whitespace)) "'") string)
  (identificador("letter" (arbno (or letter digit "?")))symbol)
  ;enteros positivos y negativos
  (numero (digit (arbno digit)) number)
  (numero ("-" digit (arbno digit)) number)
  ;flotantes positivos y negativos
  (numero (digit (arbno digit) "." digit (arbno digit)) number)
  (numero ("-" digit (arbno digit) "." digit (arbno digit)) number)
 )
)

;Especificación Sintáctica (gramática)

(define grammar-simple-interpreter
  '((program (expression) a-program)

    ;identificador
    (expression (identificador) var-exp)

    ;datos
    (expression (numero) numero-lit)
    (expression (texto) texto-lit)
    (expression (bool) bool-lit-exp)
    (bool ("true") verdadero)
    (bool ("false") falso)
    (expr-bool (bool) bool-lit)

    ;datos predefinidos
    (expression (lista) list-exp)
    (lista ("["(separated-list expression ";")"]") list)
    
    (expression (tupla) tupla-exp)
    (tupla ( "tupla" "[" (separated-list expression ";" )"]") tupl)
    
    (expression (registro) registro-exp)
    (registro ("{" (separated-list "{" identificador "=" expression "}" ";") "}") registr)
    
    (expression (expr-bool) bool-exp)
    (expr-bool ("(" expression pred-prim expression ")") pred-prim-exp)
    (pred-prim ("<") menorQue)
    (pred-prim (">") mayorQue)
    (pred-prim ("<=") menorOigualQue)
    (pred-prim (">=") mayorOigualQue)
    (pred-prim ("==") igual)
    (pred-prim ("<>") diferente)
    
    (expr-bool (oper-bin-bool "(" expr-bool expr-bool ")") bin-bool-exp)
    (oper-bin-bool ("and") boolAnd)
    (oper-bin-bool ("or") boolOr)
    
    (expr-bool (oper-un-bool "(" expr-bool ")") not-bool-lit)
    (oper-un-bool ("not") boolNot)
    
    ;estructuras de control
    (expression ("begin" "{"expression"}" ";" (arbno expression ";") "end") begin-exp) ;falta
    (expression ("si" expr-bool "entonces" expression "sino" expression "finSI") condicional-exp)
    (expression ("mientras" expr-bool "hacer" expression "fin") mientras-exp)
    (expression ("declarar" "(" (arbno identificador "=" expression ";") ")" "{" expression "}") variableLocal-exp)
    (expression ("for""(" identificador "=" expression "hasta" expression ")""hacer" expression "fin") for-exp) ;falta

    ;primitivas
     #|(expression (primitiva-unaria "("expression")") primapp-un-exp)
    (expression ("("expression primitiva-binaria expression")") primapp-bin-exp)

    (primitiva-binaria ("+") primitiva-suma)
    (primitiva-binaria ("-") primitiva-resta)
    (primitiva-binaria ("*") primitiva-multi)
    (primitiva-binaria ("/") primitiva-div)
    (primitiva-binaria ("%") primitiva-mod)
    (primitiva-binaria ("concat") primitiva-concat)
    
    (primitiva-unaria ("longitud") primitiva-longitud)
    (primitiva-unaria ("add1") primitiva-add1)
    (primitiva-unaria ("sub1") primitiva-sub1)
    
    ;hexadecimales
    (expression ("("(separated-list numero " ")")") hexa-lit)|#

    (expresion ("set" identificador "=" expresion) set-exp)
    
    ;Procedimientos
    (expression ("procedimiento" "("(separated-list identificador ",") ")" "haga" expression "finProc") procedimiento-exp);procedimiento
    
    (expression ("invocar-proc" expression "(" (separated-list expression ",") ")") procedimiento-inv-exp);invocaciÃ3n del procedimiento
    
    (expression ("proc-recursivo" (arbno identificador "(" (separated-list identificador ",") ")" "=" expression)  "in" expression)  proc-recursivo-exp);procedimiento recursivo

    (expression ("evaluar" expression "("(separated-list expression "," ) ")" "finEval" ) app-exp)
   )
)

;Construida automáticamente la sintaxis abstracta:
(sllgen:make-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)))

;*******************************************************************************************
;Parser, Scanner, Interfaz

;El FrontEnd (Análisis léxico (scanner) y sintáctico (parser) integrados)
(define scan&parse
  (sllgen:make-string-parser scanner-spec-simple-interpreter grammar-simple-interpreter))

;El Analizador Léxico (Scanner)
(define just-scan
  (sllgen:make-string-scanner scanner-spec-simple-interpreter grammar-simple-interpreter))

;El Interpretador (FrontEnd + Evaluación + señal para lectura )

(define interpretador
  (sllgen:make-rep-loop  "--❤ "
    (lambda (pgm) (eval-program  pgm)) 
    (sllgen:make-stream-parser 
      scanner-spec-simple-interpreter
      grammar-simple-interpreter)))

;*******************************************************************************************
;El Interprete

;eval-program: <programa> -> numero
; función que evalúa un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)

(define eval-program
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
                 (eval-expression body (init-env))))))

(define init-env
  (lambda ()
    (extend-env
     '(@a @b @c @d @e @f)
     '(1 2 3 "hola" "FLP")
     (empty-env))))

;Definición de targets y referencias

(define-datatype target target?
  (direct-target (expval expval?))
  (indirect-target (ref ref-to-direct-target?)))

;referencias
(define-datatype reference reference?
  (a-ref (position integer?)
         (vec vector?)))

;eval-expression: <expression> <enviroment> -> numero
; evalua la expresión en el ambiente de entrada
(define eval-expression
  (lambda (exp env)
    (cases expression exp
    ;identificadores
      (var-exp (id) (buscar-variable env id)) ;por aqui entra

    ;definiciones
      (var-def-exp (ids exps) 0) ;falta
      (const-def-exp (ids exps) 0) ;falta
      (rec-def-exp (ids exps) 0) ;falta

    ;datos
      (numero-lit (num) num)
      (texto-lit (txt) txt)
      (bool-lit-exp (bool) (eval-boolean bool))
      
    ;datos predefinidos
      (list-exp (lista) (eval-lista lista env))
      (tupla-exp (tupla) (eval-tupla tupla))
      (registro-exp (registro) (eval-registro registro))
      (bool-exp (exp) (eval-expr-bool exp)
                (cases expr-bool exp
                  (pred-prim-exp (exp-bool1 pred-prim exp-bool2)
                                 (apply-pred-prim pred-prim exp-bool1 exp-bool2 env))
                  (bin-bool-exp (exp-bool1 oper-bin-bool exp-bool2)
                                (apply-oper-bin-bool oper-bin-bool exp-bool1 exp-bool2 env))
                  (bool-lit (exp-bool) (eval-expression exp-bool env))
                  (not-bool-lit (oper-un-bool exp-bool)
                                (apply-un-bool oper-un-bool exp-bool env))
                 )
      )

      (set-exp (id rhs-exp)
               (begin-exp
                 (primitive-setref!
                  (apply-env-ref env id)
                  (eval-expresion rhs-exp env))
                 1))

    ;estructuras de control
      (begin-exp (exp exps) (if(null? exps)
                               (eval-expression exp env)
                               (begin (cons exp exps) (begin-func exps env))
      )
      (condicional-exp (test-exp true-exp false-exp)
                       (if(true-value? (eval-expression test-exp env))
                          (eval-expression true-exp env)
                          (eval-expression false-exp env)
                        )
      )
      (mientras-exp (exp-bool cuerpo) (while-loop (eval-expression exp-bool env) cuerpo env))
      (variableLocal-exp (ids exps cuerpo)
               (let ((args (eval-rands exps env)))
                 (eval-expression cuerpo
                                  (extend-env ids args env)))
      )
      (for-exp (id valorInicial limite cuerpo) (for-loop (eval-expression valorInicial env) (eval-expression limite env) cuerpo env))
      
      (app-exp (rator rands)
               (let ((proc (eval-expression rator env))
                     (args (eval-rands rands env)))
                 (if (procval? proc)
                     (apply-procedure proc args)
                     (eopl:error 'eval-expression
                                 "Attempt to apply non-procedure ~s" proc))))

    ;primitivas
      (primapp-un-exp (prim exp) (apply-un-primitive prim exp env))
      (primapp-bin-exp (exp1 prim exp2) (apply-bin-primitive exp1 prim exp2 env))

    ;hexadecimales
      (hexa-lit (hexa) (if(hexa? hexa)
                          (hexa)
                          ("No es un numero hexadecimal vÃ¡lido.")
                        )
      )

      ;procedimientos
      (procedimiento-exp (ids cuerpo)
                         (cerradura ids cuerpo env)
      )
      (procedimiento-inv-exp (expr args env)
                             (let (
                                   (proc (eval-expression expr env))
                                   (argumentos  (proc-inv-auxiliar args env))
                                   )  
                               (if (procval? proc)
                                   (apply-procedure proc argumentos)
                                   (eopl:error 'eval-expression
                                               "No se puede aplicar el procedimiento para ~s" proc))
                             )
      )
      (proc-recursivo-exp (nombre-proc idfs bodys letrec-body)
                          (proc-rec-auxiliar nombre-proc idfs bodys letrec-body env))
      )
    )
  )
)


; funciones auxiliares para aplicar eval-expression a cada elemento

;funcion auxiliar para evaluar las listas
(define eval-list
  (lambda (exp env)
    (cases expression exp
      (list-expr (lista) (eval-expression exp)))))

;funcion auxiliar para evaluar los procedimientos
(define proc-inv-auxiliar
 (lambda (exprs env)
  (cond
   ((null? exprs) empty)
   (else
      (cons (eval-expression (car exprs) env) (implementacion-exp-listas (cdr exprs) env))
   )))
)

;funcion auxiliar para implementar los procedimientos recursivos
(define proc-rec-auxiliar
  (lambda (nombre-proc idfs bodys letrec-body env)
    (eval-expression letrec-body (extend-env-recursivo nombre-proc idfs bodys env))
  )
)

;funcion auxiliar para evaluar una tupla 
(define eval-tupla
  (lambda (exp env)
    (cases expression exp
      (tupla-exp (tupla) (eval-expression exp)))))

;funcion auxiliar para evaluar un registro
(define eval-registro
  (lambda (exp env)
    (cases expression exp
      (registro-exp (registro) (eval-expression exp)))))

;funcion auxiliar para evaluar una expresion pred-prim
(define apply-pred-prim
  (lambda (expr1 pred-prim-expr exp2 env)
    (cases pred-prim pred-prim-expr
      (menorQue () (< (eval-expression exp1 env) (eval-expression exp2 env)))
      (mayorQue () (> (eval-expression exp1 env) (eval-expression exp2 env)))
      (menorOigualQue () (<= (eval-expression exp1 env) (eval-expression exp2 env)))
      (mayorOigualQue () (>= (eval-expression exp1 env) (eval-expression exp2 env)))
      (igual () (= (eval-expression exp1 env) (eval-expression exp2 env)))
      (diferente () (inexact-= (eval-expression exp1 env)))
      )
   )
 )

;funcion auxiliar para evaluar una expresion oper-bin-bool
(define apply-oper-bin-bool
  (lambda (oper-bin-bool-exp expr-bool1 expr-bool2 env)
    (cases oper-bin-bool oper-bin-bool-exp
      (boolAnd () (and (eval-expression expr-bool1 env) (eval-expression expr-bool2 env)))
      (boolNot () (or (eval-expression expr-bool1 env) (eval-expression expr-bool2 env)))
    )
  )
)

;funcion auxiliar para evaluar una expresion oper-un-bool
(define apply-un-bool
  (lambda (oper-un-bool-exp expr-bool env)
    (cases oper-un-bool oper-un-bool-exp
      (boolNot () (not (eval-expression expr-bool1 env)))
    )
  )
)

;funcion auxiliar para evaluar una expresion bool
(define eval-boolean
  (lambda (bool-expr)
    (cases bool-expr
      ((verdadero) #t)
      ((falso) #f)
    )
  )
)

;Función que retorna una lista de los números desde 0 hasta end
(define iota
  (lambda (end)
    (let
        loop ((next 0))
        (if (>= next end)
            '()
            (cons next (loop (+ 1 next)))))))

;Función para procedimientos recursivos que crea un ambiente extendido
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

; lista de operandos (expresiones)
(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

(define eval-rand
  (lambda (rand env)
    ;(eval-expression rand env)
    (cases expression rand
      (lista (exp)
             (indirect-target
              (let((ref (apply-env-ref env exp)))
                (cases target (primitive-deref ref)
                  (direct-target (expval) ref)
                  (indirect-target (ref-1) ref-1)
                  )
                )
              )
      )
      (else
        (direct-target (eval-expression rand env)))
      )))


(define eval-primapp-exp-rands
  (lambda (rands env)
    (map (lambda (x) (eval-expression x env)) rands)))

(define eval-let-exp-rands
  (lambda (rands env)
    (map (lambda (x) (eval-let-exp-rand x env))
         rands)))

(define eval-let-exp-rand
  (lambda (rand env)
    (direct-target (eval-expression rand env))))

;medir-texto: <string> -> <number>
(define medir-texto
  (lambda (exp env)
    (cases expression exp
      (texto-lit (txt) (-(string-length (eval-expression exp env))2))
      (var-exp (id) (string-length (eval-expression exp env)))
      (else (0))
    )
  )
)

;recortar-string: <string> -> <string>
(define recortar-string
  (lambda (exp env)
    (cases expression exp
      (texto-lit (txt) (substring (eval-expression exp env) 1 (- (string-length (eval-expression exp env)) 1)))
      (else (eval-expression exp env))
    )
  )
)

;true-value?: determina si un valor dado corresponde a un valor booleano falso o verdadero
(define true-value?
  (lambda (x)
    (not (zero? x))))

;************************************************************************************************
;Procedimientos
(define-datatype procval procval?
  (cerradura
   (list-ID (list-of symbol?))
   (exp expression?)
   (amb environment?)))

;apply-procedure: evalua el cuerpo de un procedimientos en el ambiente extendido correspondiente
(define apply-procedure
  (lambda (proc args)
    (cases procval proc
      (cerradura (ids cuerpo env)
               (eval-expression cuerpo (extend-env ids args env))))))

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

;*******************************************************************************************
;Ambientes

;definición del tipo de dato ambiente
(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record (syms (list-of symbol?))
                       (vals (list-of scheme-value?))

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
    (extended-env-record syms vals env)))

;función que busca un identificador en un ambiente
;Cambiar simbolo por identificador
(define buscar-variable
  (lambda (env idn) ;idn es simbolo a buscar
    (cases environment env
      (empty-env-record ()
                        (eopl:error 'apply-env "Error la variable no existe: ~s" idn))
      (extended-env-record (lista-idn vals env) ;lista-idn es lista de simbolos - vals es lista de valores
                           (let ((pos (list-find-position idn lista-idn)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (buscar-variable env idn)))))))


;funcion auxiliar que crea un ambiente extendido para los procedimientos recursivos.
(define extend-env-recursivo
  (lambda (nombre-proc idfs bodys env-viejo)
    (let ((len (length nombre-proc)))
      (let ((vec (make-vector len)))
        (let ((env (extended-env-record (map (lambda (id) (mutable id))nombre-proc) vec env-viejo)))
          (for-each
            (lambda (pos ids body)
              (vector-set! vec pos (closure ids body env))
            )
            (iota len) idfs bodys
          )
          env)))))


;****************************************************************************************
; funciones auxiliares para encontrar la posición de un símbolo
; en la lista de símbolos de unambiente
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

;se define un ambiente inicial
(define inicial-env
  (lambda ()
    (extend-env '(@a @b @c @d @e) '(1 2 3 "hola" "FLP") (empty-env))))

;****************************************************************************************
;Targets y referencias
(define expval?
  (lambda (x)
    (or (or (number? x) (procval? x) ) list? x)
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

(define primitive-deref
  (lambda (ref)
    (cases reference ref
      (a-ref (pos vec)
             (vector-ref vec pos)))))

;funcion deref
(define deref
  (lambda (ref)
    (cases target (primitive-deref ref)
      (direct-target (expval) expval)
      (indirect-target (ref-1)
                       (cases target (primitive-deref ref-1)
                         (direct-target (expval) expval)
                         (indirect-target (p)
                                          (eopl:error 'deref
                                                      "Illegal reference: ~s" ref-1)))))))


(define primitive-setref!
  (lambda (ref val)
    (cases reference ref
      (a-ref (pos vec)
             (vector-set! vec pos val)))))

;funcion setref!
(define setref!
  (lambda (ref expval)
    (let
        ((ref (cases target (primitive-deref ref)
                (direct-target (expval1) ref)
                (indirect-target (ref-1) ref-1))))
      (primitive-setref! ref (direct-target expval))
    )
  )
)