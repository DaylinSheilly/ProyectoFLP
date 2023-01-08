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
                             
    <primitiva-sobre-regis> := "(" "registro?" <tupla> ")"
                            := "(" "crear-registro" <tupla> ")"
                            := "ref-registro" ;???
                            := "set-registro" ;???
|#
#|
    Tenga en cuenta que:
    <numero>: Debe definirse para valores decimales y enteros (positivos y negativos)
    <texto>: Debe definirse para cualquier texto escrito en racket
    <identificador>: En este lenguaje todo identificador iniciará con el símbolo  @, es decir las
                     variables @x y @z son válidas
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
    ;identificadores
    (expression (identificador) var-exp)
    (identificador (letra) id) ;falta

    ;definiciones
    (expression ("var" "{" (arbno identificador"="expression ",")"}" "in" expression) var-def-exp)
    (expression ("const" "{" (arbno identificador"="expression ",")"}" "in" expression) const-def-exp)
    (expression ("rec" "{" (arbno identificador "(" "{" (arbno identificador ",") "}" ")" "="expression ",")"}" "in" expression) rec-def-exp)

    ;datos
    (expression (numero) numero-lit)
    (expression ("*"texto"*") texto-lit)
    (expression (bool) bool-exp)
    (numero () num) ;falta
    (texto () texto) ;falta
    (bool ("true") verdadero)
    (bool ("false") falso)

    ;datos predefinidos
    (expression (lista) list-exp)
    (expression (tupla) tupla-exp)
    (expression (registro) registro-exp)
    (expression (expr-bool) bool-exp)
    (lista ("["(separated-list expression ";")"]") lista)
    (tupla ( "tupla" "[" (separated-list expression ";" )"]") tupla)
    (registro ("{" (separated-list "{" identificador "=" expression "}" ";") "}") registro)

    (expr-bool ("(" expression pred-prim expression ")") pred-prim-exp)
    (expr-bool ("(" expr-bool oper-bin-bool expr-bool ")") bin-bool-exp)
    (expr-bool (bool) bool-lit)
    (expr-bool (oper-un-bool "(" expr-bool ")") not-bool-lit)

    (pred-prim ("<") menorQue)
    (pred-prim (">") mayorQue)
    (pred-prim ("<=") menorOigualQue)
    (pred-prim (">=") mayorOigualQue)
    (pred-prim ("==") igual)
    (pred-prim ("<>") diferente)

    (oper-bin-bool ("and") y)
    (oper-bin-bool ("or") o)

    (oper-un-bool ("not") negacion)

    ;estructuras de control
    (expression ("begin" {expression}(arbno ";" expression) "end") begin-exp) ;falta
    (expression ("si" expr-bool "entonces" expression "sino" expression "finSI") condicional-exp)
    (expression ("mientras" expr-bool "hacer" expression "fin") mientras-exp)
    (expression ("declarar" "(" (arbno identificador "=" expression ";") ")" "{" expression "}") variableLocal-exp)
    (expression ("for""(" identificador "=" expression "hasta" expression ")""hacer" expression "fin") for-exp) ;falta

    ;primitivas
    (expression (primitiva-unaria "("expression")") primapp-un-exp)
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
    (expression ("("(separated-list numero " ")")") hexa-lit)

    ;Procedimientos
    (expression ("procedimiento" "("(separated-list identificador ",") ")" "haga" expresion "finProc") procedimiento-exp);procedimiento
    
    (expression ("invocar-proc" expresion "(" (separated-list expresion ",") ")") procedimiento-inv-exp);invocación del procedimiento
    
    (expression ("proc-recursivo" (arbno identificador "(" (separated-list identificador ",") ")" "=" expresion)  "in" expresion)  proc-recursivo-exp);procedimiento recursivo

    ;???
    ;(expression ("evaluar" expression "("(separated-list expression "," ) ")" "finEval" ) app-exp)

    ;Asignación

    (expression ("set" identifier "=" expression) set-exp)

    
   )
)

;Tipos de datos para la sintaxis abstracta de la gramática

;Construidos manualmente:

;(define-datatype program program?
;  (a-program
;   (exp expression?)))
;
;(define-datatype expression expression?
;  (lit-exp
;   (datum number?))
;  (var-exp
;   (id symbol?))
;  (primapp-exp
;   (prim primitive?)
;   (rands (list-of expression?)))
;  (if-exp
;   (test-exp expression?)
;   (true-exp expression?)
;   (false-exp expression?))
;  (let-exp
;   (ids (list-of symbol?))
;   (rans (list-of expression?))
;   (body expression?)))
;
;(define-datatype primitive primitive?
;  (add-prim)
;  (substract-prim)
;  (mult-prim)
;  (incr-prim)
;  (decr-prim))

;Construida automáticamente la sintaxis abstracta:

(sllgen:make-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)))


;Función para buscar dentro un ambiente (referencia)
(define apply-env
  (lambda (env var)
    (deref (apply-env-ref env var))))

;Funcion para retornar una referencia (implicita)
(define apply-env-ref
  (lambda (env var)
    (cases ambiente env
      (ambiente-vacio () (eopl:error "No se encuentra la ligadura " var))
      (ambiente-extendido
       (lid lval old-env)
       (letrec
           (
            (buscar-id
             (lambda (lidd lvall varr pos)
               (cond
                 [(null? lidd) (apply-env-ref old-env varr)]
                 [(eqv? (car lidd) varr) (a-ref pos lvall)] ;;Ya no retorno el valor si no la referencia
                 [else (buscar-id (cdr lidd) lvall varr (+ pos 1))])))
            )
         (buscar-id lid lval var 0)))
      (ambiente-extendido-recursivo
       (proc-names llargs bodies env-old)
       (letrec
           (
            (buscar-proc
             (lambda (proc-names llargs bodies)
               (cond
                 [(null? proc-names)
                  (apply-env-ref env-old var)]
                 [(eqv?
                   (car proc-names)
                   var)
                  (a-ref
                   0
                   (list->vector 
                    (list(cerradura
                    (car llargs)
                    (car bodies)
                    env)))) ;Aqui generamos la clausura
                  ]
                 [else
                  (buscar-proc (cdr proc-names)
                               (cdr llargs)
                               (cdr bodies))])))
            )
         (buscar-proc proc-names llargs bodies)))
      )
    )
  )




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
      (bool-lit (bool) (eval-boolean bool))
      
    ;datos predefinidos
      (list-exp (lista) (eval-lista lista))
      (tupla-exp (tupla) (eval-tupla tupla))
      (registro-exp (registro) (eval-registro registro))
      (bool-exp (exp) (eval-expr-bool exp))

    ;estructuras de control
      (begin-exp (exp exps) 0) ;falta
      (condicional-exp (test-exp true-exp false-exp)
                       (if(true-value? (eval-expression test-exp env))
                          (eval-expression true-exp env)
                          (eval-expression false-exp env)
                        )
      )
      (mientras-exp (exp-bool cuerpo) 0) ;falta
      (variableLocal-exp (ids exps cuerpo)
               (let ((args (eval-rands exps env)))
                 (eval-expression cuerpo
                                  (extend-env ids args env)))
      )
      (for-exp (id valorInicial limite cuerpo) 0) ;falta
      
      #|(app-exp (rator rands)
               (let ((proc (eval-expression rator env))
                     (args (eval-rands rands env)))
                 (if (procval? proc)
                     (apply-procedure proc args)
                     (eopl:error 'eval-expression
                                 "Attempt to apply non-procedure ~s" proc))))|#

    ;primitivas
      (primapp-un-exp (prim exp) (apply-un-primitive prim exp env))
      (primapp-bin-exp (exp1 prim exp2) (apply-bin-primitive exp1 prim exp2 env))

    ;hexadecimales
      (hexa-lit (hexa) (if(hexa? hexa)
                          (hexa)
                          ("No es un numero hexadecimal válido.")
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
                          (proc-rec-auxiliar nombre-proc idfs bodys letrec-body env)
      )


      ;Asignacion
      (set-exp (id exp)
               (let
                   (
                    (ref (apply-env-ref env id))
                    (val (eval-expression exp env))
                    )
                 (begin
                   (set-ref! ref val)
                   0)
                 )
               )


      
)))

; funciones auxiliares para aplicar eval-expression a cada elemento de una

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

(define eval-tupla
  (lambda (exp env)
    (cases expression exp
      (tupla-exp (tupla) (eval-expression exp)))))


(define eval-registro
  (lambda (exp env)
    (cases expression exp
      (registro-exp (registro) (eval-expression exp)))))


(define eval-expr-bool
  (lambda (expr-bool env)
    (cases expression expr-bool
      #|(primapp-un-exp (prim-unaria exp)
                      (apply-un-primitive prim-unaria exp env))
      (primapp-bin-bool (exp1 prim-binaria exp2)
                       (apply-bin-primitive exp1 prim-binaria exp2 env))|#
      ;(pred-prim-exp)
      ;bool
      )))

; lista de operandos (expresiones)
(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

(define eval-rand
  (lambda (rand env)
    (eval-expression rand env)))

;apply-un-primitive: <primitiva-unaria> (<expression>) -> numero
(define apply-un-primitive
  (lambda (prim-unaria exp env)
    (cases primitiva-unaria prim-unaria
      (primitiva-longitud () (medir-texto exp env))
      (primitiva-add1 () (+ (eval-expression exp env) 1))
      (primitiva-sub1 () (- (eval-expression exp env) 1)))))

;apply-bin-primitive: (<expression> <primitiva-binaria> <expression>) -> numero
(define apply-bin-primitive
  (lambda (exp1 prim-binaria exp2 env)
    (cases primitiva-binaria prim-binaria
      (primitiva-suma () (+ (eval-expression exp1 env) (eval-expression exp2 env)))
      (primitiva-resta () (- (eval-expression exp1 env) (eval-expression exp2 env)))
      (primitiva-multi () (* (eval-expression exp1 env) (eval-expression exp2 env)))
      (primitiva-div () (/ (eval-expression exp1 env) (eval-expression exp2 env)))
      (primitiva-concat () (string-append (recortar-string exp1 env) (recortar-string exp2 env)))
    )
  )
)

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
;Funciones Auxiliares

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
