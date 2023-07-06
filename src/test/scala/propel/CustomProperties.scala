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
      (type bool {True False})
      (type nat {Z (S nat)})
      (type list {Nil (Cons nat list)})

      (type GCounter {(GCounter nat)})

      (type PNCounter {(PNCounter GCounter GCounter)})
      (type PNCounter2 {(PNCounter2 nat nat)})

      (type LWWReg {(LWWReg nat nat)}) ; LWWReg value timestamp

      (type LWWRegOp {(Assign nat nat)}) ; Assign value timestamp

      (type GOp {GInc})
      (type PNOp {PNInc PNDec})

      (type LWWMap (fun nat {(None nat)       ; time of last delete
                             (Just LWWReg)})) ; maps key to optional LWWReg

      (type LWWMapOp {(Set nat nat nat) ; set timestamp key value
                      (Delete nat nat)  ; delete timestamp key (key needed because we don't
                                        ; assume uniqueness of timestamp)
                     })

      (def eq? (fun nat nat bool)
        (lambda [refl sym antisym] (x nat) (y nat)
          (cases (Pair x y)
            [(Pair Z Z) True]
            [(Pair (S a) (S b)) (eq? a b)]
            [_ False])))

      (def leq? (fun nat nat bool)
        (lambda [conn refl antisym trans] (x nat) (y nat)
          (cases (Pair x y)
            [(Pair Z _) True]
            [(Pair (S _) Z) False]
            [(Pair (S a) (S b)) (leq? a b)])))

      (def max (fun nat nat nat)
        (lambda [comm assoc idem] (x nat) (y nat)
          (if (leq? x y) y x)))

      (def applyG (fun GOp GCounter GCounter)
        (lambda (o GOp) (x GCounter)
          (cases x
            [(GCounter n) (GCounter (S n))])))

      (def applyPN (fun PNOp PNCounter PNCounter)
        (lambda (o PNOp) (x PNCounter)
          (cases (Pair o x)
            [(Pair PNInc (PNCounter x y)) (PNCounter (applyG GInc x) y)]
            [(Pair PNDec (PNCounter x y)) (PNCounter x (applyG GInc y))])))

      (def applyPN2 (fun PNOp PNCounter2 PNCounter2)
        (lambda (o PNOp) (x PNCounter2)
          (cases (Pair o x)
            [(Pair PNInc (PNCounter2 x y)) (PNCounter2 (S x) y)]
            [(Pair PNDec (PNCounter2 x y)) (PNCounter2 x (S y))])))

      (def applyLWWReg (fun LWWRegOp LWWReg LWWReg)
        (lambda (o LWWRegOp) (r LWWReg)
          (cases (Pair o r)
            [(Pair (Assign new newtime) (LWWReg old oldtime))
             (if (eq? oldtime newtime)
                 (LWWReg (max new old) newtime)
                 (if (leq? oldtime newtime)
                     (LWWReg new newtime)
                     (LWWReg old oldtime)))])))

      (def applyLWWMap (fun LWWMapOp LWWMap LWWMap)
        (lambda (o LWWMapOp) (map LWWMap)
          (cases o
            [(Set timestamp key value)
             (lambda (key2 nat) (if (eq? key key2)
                                    (cases (map key)
                                      [(None delete) (if (leq? timestamp delete)
                                                         (None delete)
                                                         (Just (LWWReg value timestamp)))]
                                      [(Just (LWWReg oldvalue oldtimestamp))
                                       (if (eq? timestamp oldtimestamp)
                                           (Just (LWWReg (max oldvalue value) timestamp))
                                           (if (leq? oldtimestamp timestamp)
                                               (Just (LWWReg value timestamp))
                                               (Just (LWWReg oldvalue oldtimestamp))))])
                                    (map key2)))]
            [(Delete timestamp key)
             (lambda (key2 nat) (if (eq? key key2)
                                    (cases (map key)
                                      [(None delete) (None (max timestamp delete))]
                                      [(Just (LWWReg oldvalue oldtimestamp))
                                       (if (leq? oldtimestamp timestamp)
                                           (None timestamp)
                                           (map key))])
                                    (map key2)))])))


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

  val exampleOpBasedGCounter = properties.addCustomProperty(
    parser.deserialize("(applyG o1 (applyG o2 x))").get,
    parser.deserialize("(applyG o2 (applyG o1 x))").get,
    Set(Symbol("o1"), Symbol("o2"), Symbol("x")),
    Symbol("applyG"),
    example)

  val exampleOpBasedPNCounter = properties.addCustomProperty(
    parser.deserialize("(applyPN o1 (applyPN o2 x))").get,
    parser.deserialize("(applyPN o2 (applyPN o1 x))").get,
    Set(Symbol("o1"), Symbol("o2"), Symbol("x")),
    Symbol("applyPN"),
    exampleOpBasedGCounter)

  val exampleOpBasedPN2Counter = properties.addCustomProperty(
    parser.deserialize("(applyPN2 o1 (applyPN2 o2 x))").get,
    parser.deserialize("(applyPN2 o2 (applyPN2 o1 x))").get,
    Set(Symbol("o1"), Symbol("o2"), Symbol("x")),
    Symbol("applyPN2"),
    exampleOpBasedPNCounter)

  val exampleOpBasedLWWReg = properties.addCustomProperty(
    parser.deserialize("(applyLWWReg o1 (applyLWWReg o2 x))").get,
    parser.deserialize("(applyLWWReg o2 (applyLWWReg o1 x))").get,
    Set(Symbol("o1"), Symbol("o2"), Symbol("x")),
    Symbol("applyLWWReg"),
    exampleOpBasedPN2Counter)

  val exampleOpBasedLWWMap = properties.addCustomProperty(
    parser.deserialize("(applyLWWMap o1 (applyLWWMap o2 x))").get,
    parser.deserialize("(applyLWWMap o2 (applyLWWMap o1 x))").get,
    Set(Symbol("o1"), Symbol("o2"), Symbol("x")),
    Symbol("applyLWWMap"),
    exampleOpBasedLWWReg)

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

  val errors = properties.check(exampleOpBasedLWWMap, printDeductionDebugInfo = false, printReductionDebugInfo = false).showErrors
  if errors.nonEmpty then
    println(errors)
