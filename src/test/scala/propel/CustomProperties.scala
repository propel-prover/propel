package propel

import ast.dsl.*
import ast.dsl.sugar.*
import printing.*
import evaluator.*

@main def custom =
//  val example = parser.deserialize(
//    """
//      (def return (lambda T (x T) (Cons x Nil)))
//      (def append (lambda T
//        (letrec append (fun (rec List {Nil (Cons T List)}) (rec List {Nil (Cons T List)}) (rec List {Nil (Cons T List)}))
//          (lambda (x (rec List {Nil (Cons T List)})) (y (rec List {Nil (Cons T List)}))
//            (cases x
//              [Nil y]
//              [(Cons x xs) (Cons x (append xs y))]))
//          append)))
//      (def >>= (lambda T U
//        (letrec >>=_internal (fun (rec List {Nil (Cons T List)}) (fun T (rec List {Nil (Cons U List)})) (rec List {Nil (Cons U List)}))
//          (lambda (x (rec List {Nil (Cons T List)})) (f (fun T (rec List {Nil (Cons U List)})))
//            (cases x
//              [Nil Nil]
//              [(Cons x xs) (append [U] (f x) (>>=_internal xs f))]))
//          >>=_internal)))
//
//;      (lambda A B C (l (rec List {Nil (Cons A List)})) (g (fun A (rec List {Nil (Cons B List)}))) (h (fun B (rec List {Nil (Cons C List)})))
//;        (Equal?
//;          (>>= [B C] (>>= [A B] l g) h)
//;          (>>= [A C] l (lambda (x A) (>>= [B C] (g x) h)))
//;        ))
//    """).get


  val example = parser.deserialize(
    """
      (type nat {Z (S nat)})
      (type list {Nil (Cons nat list)})

      (def return (lambda (x nat) (Cons x Nil)))

      (def append (fun list list list)
        (lambda (x list) (y list)
          (cases x
            [Nil y]
            [(Cons x xs) (Cons x (append xs y))])))

      (def >>= (fun list (fun nat list) list)
        (lambda (x list) (f (fun nat list))
          (cases x
            [Nil Nil]
            [(Cons x xs) (append (f x) (>>= xs f))])))

;      (lambda (l list) (g (fun nat list)) (h (fun nat list))
;        (Equal?
;          (>>= (>>= l g) h)
;          (>>= l (lambda (x nat) (>>= (g x) h)))
;        ))
    """).get

//  val exampleWithProperties = properties.addCustomProperty(
//    parser.deserialize("(>>= (>>= l g) h)").get,
//    parser.deserialize("(>>= l (lambda (x nat) (>>= (g x) h)))").get,
//    Set(Symbol("l"), Symbol("g"), Symbol("h")),
//    Symbol(">>="),
//    example)

  val exampleWithProperties0 = properties.addCustomProperty(
    parser.deserialize("(>>= (return x) g)").get,
    parser.deserialize("(g x)").get,
    Set(Symbol("x"), Symbol("g")),
    Symbol(">>="),
    example)

  val exampleWithProperties = properties.addCustomProperty(
    parser.deserialize("(>>= l return)").get,
    parser.deserialize("l").get,
    Set(Symbol("l")),
    Symbol(">>="),
    exampleWithProperties0)

  val errors = properties.check(exampleWithProperties, printDeductionDebugInfo = false, printReductionDebugInfo = false).showErrors
  if errors.nonEmpty then
    println(errors)
