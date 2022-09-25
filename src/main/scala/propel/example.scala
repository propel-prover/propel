package propel

import ast.*
import dsl.*
import dsl.sugar.*
import printing.*
import typer.*
import evaluator.*


def merge[A: TermExpr](expr: A) =
  letrec(
    "merge" -> forall("T")(("T" -> ("T" -> bool)) -> (("T" -> ("T" -> bool)) -> (list("T") -> (list("T") -> list("T"))))) ->
      tpabs("T")(abs(comm)("eq" -> tp("T" -> ("T" -> bool)), "lt" -> tp("T" -> ("T" -> bool)), "a" -> list("T"), "b" -> list("T"))(
        cases("Pair", "a", "b")(
          ("Pair", "Nil", "Nil") -> "Nil",
          ("Pair", ("Cons", "a", "as"), "Nil") -> ("Cons", "a", "as"),
          ("Pair", "Nil", ("Cons", "b", "bs")) -> ("Cons", "b", "bs"),
          ("Pair", ("Cons", "a", "as"), ("Cons", "b", "bs")) ->
            `if`("eq", "a", "b")
                ("Cons", "a", ("Cons", "b", (tpapp("merge")(tp("T")), "eq", "lt", "as", "bs")))
                (`if`("lt", "a", "b")
                     ("Cons", "a", (tpapp("merge")(tp("T")), "eq", "lt", "as", ("Cons", "b", "bs")))
                     ("Cons", "b", (tpapp("merge")(tp("T")), "eq", "lt", ("Cons", "a", "as"), "bs")))))))(
    expr)

def min[A: TermExpr](expr: A) =
  letrec(
    "min" -> tp(nat -> (nat -> nat)) -> abs(assoc, comm)("a" -> nat, "b" -> nat)(cases("Pair", "a", "b")(
      ("Pair", ("S", "a"), ("S", "b")) -> ("S", app(assoc, comm)("min", "a", "b")),
      ("_") -> "Z")))(
    expr)

def max[A: TermExpr](expr: A) =
  letrec(
    "max" -> tp(nat -> (nat -> nat)) -> abs(assoc, comm)("a" -> nat, "b" -> nat)(cases("Pair", "a", "b")(
      ("Pair", ("S", "a"), ("S", "b")) -> ("S", app(assoc, comm)("max", "a", "b")),
      ("Pair", "a", "Z") -> "a",
      ("Pair", "Z", "a") -> "a")))(
    expr)

def ordernat[A: TermExpr](expr: A) =
  letrec(
    "ordernat" -> tp(nat -> (nat -> bool)) -> abs(antisym, trans)("a" -> nat, "b" -> nat)(let("pair" -> ("Pair", "a", "b"))(
      cases("pair")(
        ("Pair", ("S", "x"), ("S", "y")) -> app(antisym, trans)("ordernat", "x", "y"),
        ("Pair", "Z", "_") -> True,
        ("_") -> False))))(
    expr)

def orderlist[A: TermExpr](expr: A) =
  letrec(
    "orderlist" -> tp(list(nat) -> (list(nat) -> bool)) ->
      abs(antisym, trans)("a" -> list(nat), "b" -> list(nat))(let("pair" -> ("Pair", "a", "b"))(
        cases("pair")(
          ("Pair", ("Cons", ("S", "x"), "xs"), ("Cons", ("S", "y"), "ys")) ->
            app(antisym, trans)("orderlist", ("Cons", "x", "xs"), ("Cons", "y", "ys")),
          ("Pair", ("Cons", "Z", "xs"), ("Cons", "Z", "ys")) ->
            app(antisym, trans)("orderlist", "xs", "ys"),
          ("Pair", ("Cons", "Z", "xs"), ("Cons", "_", "_")) ->
            True,
          ("Pair", "Nil", "_") ->
            True,
          ("_") ->
            False))))(
    expr)

def map[A: TermExpr](expr: A) =
  letrec(
    "map" -> forall("T")(("T" -> ("T" -> "T")) -> (list("T") -> (list("T") -> list("T")))) ->
      tpabs("T")(abs("f" -> tp("T" -> ("T" -> "T")))(abs(comm)("a" -> list("T"), "b" -> list("T"))(cases("Pair", "a", "b")(
        ("Pair", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
          ("Cons", app(comm)("f", "x", "y"), app(comm)((tpapp("map")(tp("T")), "f"), "xs", "ys")),
        ("_") ->
          "Nil")))))(
    expr)

def plus[A: TermExpr](expr: A) =
  letrec(
    "+" -> tp(nat -> (nat -> nat)) ->
      abs(assoc, comm)("a" -> nat, "b" -> nat)(cases("Pair", "a", "b")(
        ("Pair", "Z", "b") -> "b",
        ("Pair", "a", "Z") -> "a",
        ("Pair", ("S", "a"), ("S", "b")) -> ("S", ("S", app(assoc, comm)("+", "a", "b")))))) (
    expr)

def mult[A: TermExpr](expr: A) =
  letrec(
    "*" -> tp(nat -> (nat -> nat)) ->
      abs(assoc, comm)("a" -> nat, "b" -> nat)(cases("a")(
        ("S", "a") -> app(assoc, comm)("+", app(assoc, comm)("*", "a", "b"), "b"),
        "_" -> "Z")))(
    expr)


def bv_succ[A: TermExpr](expr: A) =
    letrec(
        "bv_succ" -> tp(bv -> bv) ->
            abs()("a" -> bv)(cases("a")(
                "BZ" -> ("B1", "BZ"),
                ("B0", "x") -> ("B1", "x"),
                ("B1", "x") -> ("B0", ("bv_succ", "x")))))  (expr)

def bv_plus[A: TermExpr](expr: A) =
    letrec(
        "bv_plus" -> tp(bv -> (bv -> bv)) ->
            abs(assoc, comm)("a" -> bv, "b" -> bv)(cases("Pair", "a", "b")(
                ("Pair", "BZ", "x") -> "x",
                ("Pair", "x", "BZ") -> "x",
                ("Pair", ("B0", "x"), ("B0", "y")) -> ("B0", app(assoc, comm)("bv_plus", "x", "y")),
                ("Pair", ("B0", "x"), ("B1", "y")) -> ("B1", app(assoc, comm)("bv_plus", "x", "y")),
                ("Pair", ("B1", "x"), ("B0", "y")) -> ("B1", app(assoc, comm)("bv_plus", "x", "y")),
                ("Pair", ("B1", "x"), ("B1", "y")) -> ("B0", ("bv_succ", app(assoc, comm)("bv_plus", "x", "y")))
                )))(expr)

def gcounter_merge[A: TermExpr](expr: A) =
    letrec("gcounter_merge" -> tp(list(nat) -> (list(nat) -> list(nat))) ->
        abs(assoc, comm)("a" -> list(nat), "b" -> list(nat))(cases("Pair", "a", "b")(
            ("Pair", ("Cons", "ah", "as"), ("Cons", "bh", "bs")) ->
                ("Cons", app(assoc,comm)("max", "ah", "bh"), app(assoc,comm)("gcounter_merge", "as", "bs")),
            (("Pair", "x", "Nil") -> "x"),
            (("Pair", "Nil", "y") -> "y")
        )))(expr)

def pncounter_merge[A: TermExpr](expr: A) =
    val pncounter = dt("Pair", list(nat), list(nat))
    let("pncounter_merge" -> abs(assoc, comm)("a" -> pncounter, "b" -> pncounter)(
            let(("Pair", ("Pair", "a1", "a2"), ("Pair", "b1", "b2")) -> ("Pair", "a", "b"))
               ("Pair", app(comm,assoc)("gcounter_merge", "a1", "b1"), app(comm,assoc)("gcounter_merge", "a2", "b2"))
        ))(expr)

// RFC677 describes it to be commutative
def lwwreg_merge[A: TermExpr](expr: A) =
    val lwwreg = dt("Pair", nat, nat)
    val withOrd = false
    val withAcc = false
    
    if withOrd // TODO ordernat must also be reflexive so ordernat(t2,t2)=False is a contradiction
    // result: commutativity: no, associativity: no
    then
        let("lwwreg_merge" -> abs(assoc,comm)("a" -> lwwreg, "b" -> lwwreg)(
            let(("Pair", ("Pair", "d1", "t1"), ("Pair", "d2", "t2")) -> ("Pair", "a", "b"))
                (`if`(app(antisym, trans)("ordernat", "t1", "t2"))
                     (`if`(app(antisym, trans)("ordernat", "t2", "t1"))
                          ("Pair", app(comm,assoc)("max", "d1", "d2"), "t1")
                          ("Pair", "d2", "t2"))
                     ("Pair", "d1", "t1"))))(expr)
    else if withAcc // commutativity: no, associativity: no
    then
        letrec("lwwreg_merge" -> tp(lwwreg -> (lwwreg -> lwwreg)) ->
            abs(comm,assoc)("a" -> lwwreg, "b" -> lwwreg)(
                (letrec("aux" -> tp(nat -> (lwwreg -> (lwwreg -> lwwreg))) ->
                    abs()("acc" -> nat)(abs(comm,assoc)("a" -> lwwreg, "b" -> lwwreg)(cases("Pair", "a", "b")(
                        ("Pair", ("Pair", "d1", "Z"), ("Pair", "d2", "Z")) ->
                            ("Pair", app(comm,assoc)("max", "d1", "d2"), "acc"),
                        ("Pair", ("Pair", "d1", ("S","t1")), ("Pair", "d2", "Z")) ->
                            ("Pair", "d1", ("S", "t1")),
                        ("Pair", ("Pair", "d1", "Z"), ("Pair", "d2", ("S","t2"))) ->
                            ("Pair", "d2", ("S", "t2")),
                        ("Pair", ("Pair", "d1", ("S", "t1")), ("Pair", "d2", ("S", "t2"))) ->
                            app(comm,assoc)(("aux", ("S", "acc")), ("Pair", "d1", "t1"), ("Pair", "d2", "t2"))))))
                (app(comm,assoc)(("aux", "Z"), "a", "b")))))(expr)
    else  // associativity: no, commutativity: yes
        letrec("lwwreg_merge" -> tp(lwwreg -> (lwwreg -> lwwreg)) ->
            abs(assoc,comm)("a" -> lwwreg, "b" -> lwwreg)(cases("Pair", "a", "b")(
                ("Pair", ("Pair", "d1", "Z"), ("Pair", "d2", "Z")) ->
                    ("Pair", app(comm,assoc)("max", "d1", "d2"), "Z"),
                ("Pair", ("Pair", "d1", ("S","t1")), ("Pair", "d2", "Z")) ->
                    ("Pair", "d1", ("S", "t1")),
                ("Pair", ("Pair", "d1", "Z"), ("Pair", "d2", ("S","t2"))) ->
                    ("Pair", "d2", ("S", "t2")),
                ("Pair", ("Pair", "d1", ("S", "t1")), ("Pair", "d2", ("S", "t2"))) ->
                    let(("Pair", "d", "t") -> app(comm,assoc)("lwwreg_merge", ("Pair", "d1", "t1"), ("Pair", "d2", "t2")))
                    ("Pair", "d", ("S", "t")))))(expr)

def gset_merge[A: TermExpr](expr: A) =
    // TODO fails because we do not equate functions (implement extensionality)
    let("gset_merge" ->
        abs(comm,assoc)("a" -> tp(nat -> bool), "b" -> tp(nat -> bool))
           (abs()("x" -> nat)(or("a", "x")("b", "x"))))(expr)


@main def example =
  def check(expr: Term) =
    val result = properties.check(expr, printDeductionDebugInfo = false, printReductionDebugInfo = false)
    val errors = result.showErrors
    if errors.nonEmpty then
      println()
      println(errors)

  check(ordernat("Z"))
  println()
  check(orderlist("Z"))
  println()
  check(min("Z"))
  println()
  check(max("Z"))
  println()
  check(map("Z"))
  println()
  check(plus("Z"))
  println()
  check(plus(mult("Z")))
  println()
  check(bv_succ(bv_plus("Z")))

  check(max(gcounter_merge("Z")))
  println()
  check(max(gcounter_merge(pncounter_merge("Z"))))
  // println()
  // check(max(ordernat(lwwreg_merge("Z"))))
  // println()
  // check(gset_merge("Z"))
