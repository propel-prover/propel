package propel

import ast.*
import dsl.*
import dsl.sugar.*
import printing.*
import typer.*
import evaluator.*
import evaluator.properties.Normalization


def merge[A: TermExpr](expr: A) =
  letrec(
    "merge" -> forall("T")(("T" -> ("T" -> bool)) -> (("T" -> ("T" -> bool)) -> (list("T") -> (list("T") -> list("T"))))) ->
      tpabs("T")(abs(comm)("eq" -> tp("T" -> ("T" -> bool)), "lt" -> tp("T" -> ("T" -> bool)), "a" -> list("T"), "b" -> list("T"))(
        cases("Pair", "a", "b")( ("Pair", "Nil", "Nil") -> "Nil",
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
    "ordernat" -> tp(nat -> (nat -> bool)) -> abs(refl, antisym, conn, trans)("a" -> nat, "b" -> nat)(let("pair" -> ("Pair", "a", "b"))(
      cases("pair")(
        ("Pair", ("S", "x"), ("S", "y")) -> app(refl, antisym, conn, trans)("ordernat", "x", "y"),
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

def bv_eq[A: TermExpr](expr: A) =
    letrec("bv_eq" -> tp(bv -> tp(bv -> bool)) ->
        // INFO Z and (B0 Z) are not equal
        abs(refl, sym, trans, antisym)("a" -> bv, "b" -> bv)(cases("Pair", "a", "b")(
            ("Pair", "BZ", "BZ") -> True,
            ("Pair", ("B0", "a"), ("B0", "b")) -> app(refl, sym, trans, antisym)("bv_eq", "a", "b"),
            ("Pair", ("B1", "a"), ("B1", "b")) -> app(refl, sym, trans, antisym)("bv_eq", "a", "b"),
            ("Pair", "_1", "_2") -> False)))(expr)


def orderbv[A: TermExpr](expr: A) =
    letrec("orderbv" -> tp(bv -> tp(bv -> bool)) ->
        abs(refl, conn, antisym, trans)("a" -> bv, "b" -> bv)(cases("Pair", "a", "b")(
            ("Pair", "BZ", "_") -> True,
            ("Pair", "_", "BZ") -> False,
            ("Pair", ("B0", "a"), ("B0", "b")) -> app(refl, conn, trans, antisym)("orderbv", "a", "b"),
            ("Pair", ("B0", "a"), ("B1", "b")) -> app(refl, conn, trans, antisym)("orderbv", "a", "b"),
            ("Pair", ("B1", "a"), ("B0", "b")) -> `and`(app(refl, conn, trans, antisym)("orderbv", "a", "b"))
                                                       (`not`(app(refl, sym, trans, antisym)("bv_eq", "a", "b"))),
            ("Pair", ("B1", "a"), ("B1", "b")) -> app(refl, conn, trans, antisym)("orderbv", "a", "b"))))(expr)

def bv_max[A: TermExpr](expr: A) =
    letrec("bv_max" -> tp(bv -> (bv -> bv)) ->
        abs(assoc, comm, sel)("a" -> bv, "b" -> bv)(cases("Pair", "a", "b")(
            ("Pair", "BZ", "b") -> "b",
            ("Pair", "a", "BZ") -> "a",
            ("Pair", ("B0", "a"), ("B0", "b")) -> ("B0", app(assoc, comm, sel)("bv_max", "a", "b")),
            ("Pair", ("B1", "a"), ("B1", "b")) -> ("B1", app(assoc, comm, sel)("bv_max", "a", "b")),
            ("Pair", ("B0", "a"), ("B1", "b")) ->
                `if`(app(refl, sym, trans, antisym)("bv_eq", app(assoc, comm, sel)("bv_max", "a", "b"), "b"))
                    ("B1", "b")
                    ("B0", "a"),
            ("Pair", ("B1", "a"), ("B0", "b")) ->
                `if`(app(refl, sym, trans, antisym)("bv_eq", app(assoc, comm, sel)("bv_max", "a", "b"), "a"))
                    ("B1", "a")
                    ("B0", "b"))))(expr)


def bvu_eq[A: TermExpr](expr: A) =
    let("bvu_eq" -> abs(refl, sym, antisym, trans)("a" -> bvu, "b" -> bvu)(cases("Pair", "a", "b")(
            ("Pair", "BZ", "BZ") -> True,
            ("Pair", ("B1", "bva"), ("B1", "bvb")) -> app(refl, sym, trans, antisym)("bv_eq", "bva", "bvb"),
            ("Pair", "_1", "_2") -> False)))(expr)

def ordbvu[A: TermExpr](expr: A) =
    letrec("ordbvu" -> tp(bvu -> tp(bvu -> bool)) ->
        abs(refl, antisym, trans, conn)("a" -> bvu, "b" -> bvu)(cases("Pair", "a", "b")(
            ("Pair", "BZ", "_") -> True,
            ("Pair", "_", "BZ") -> False,
            ("Pair", ("B1", "BZ"), ("B1", "_")) -> True,
            ("Pair", ("B1", "_"), ("B1", "BZ")) -> False,
            ("Pair", ("B1", ("B0", "a")), ("B1", ("B1", "b"))) -> False,
            ("Pair", ("B1", ("B1", "a")), ("B1", ("B0", "b"))) -> True,
            ("Pair", ("B1", ("B0", "a")), ("B1", ("B0", "b"))) ->
                app(refl, antisym, trans, conn)("ordbvu", ("B1", "a"), ("B1", "b")),
            ("Pair", ("B1", ("B1", "a")), ("B1", ("B1", "b"))) ->
                app(refl, antisym, trans, conn)("ordbvu", ("B1", "a"), ("B1", "b")))))(expr)



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
    val withAcc = true
    
    if withOrd
    then
        let("lwwreg_merge" -> abs(assoc,comm)("a" -> lwwreg, "b" -> lwwreg)(
            let(("Pair", ("Pair", "d1", "t1"), ("Pair", "d2", "t2")) -> ("Pair", "a", "b"))
                (`if`(app(refl, antisym, conn, trans)("ordernat", "t1", "t2"))
                     (`if`(app(refl, antisym, conn, trans)("ordernat", "t2", "t1"))
                          ("Pair", app(comm,assoc)("max", "d1", "d2"), "t1")
                          ("Pair", "d2", "t2"))
                     ("Pair", "d1", "t1"))))(expr)
    else if withAcc // commutativity: yes, associativity: no (because `aux acc` is not associative for an arbitrary `acc`)
    then
        // HipSpec has taken more than 2hours as of the time of writing this comment and probably won't
        // prove nor disprove commutativity nor associativity
        let("lwwreg_merge" -> abs()("a" -> lwwreg, "b" -> lwwreg)(
            (letrec("aux" -> tp(nat -> (lwwreg -> (lwwreg -> lwwreg))) ->
                abs()("acc" -> nat)(abs(comm,assoc)("a" -> lwwreg, "b" -> lwwreg)(cases("Pair", "a", "b")(
                    ("Pair", ("Pair", "d1", "Z"), ("Pair", "d2", "Z")) ->
                        ("Pair", app(comm,assoc)("max", "d1", "d2"), "acc"),
                    ("Pair", ("Pair", "d1", ("S","t1")), ("Pair", "d2", "Z")) ->
                        ("Pair", "d1", app(comm,assoc)("+", "acc", ("S", "t1"))),
                    ("Pair", ("Pair", "d1", "Z"), ("Pair", "d2", ("S","t2"))) ->
                        ("Pair", "d2", app(comm,assoc)("+", "acc", ("S", "t2"))),
                    ("Pair", ("Pair", "d1", ("S", "t1")), ("Pair", "d2", ("S", "t2"))) ->
                        app(comm,assoc)(("aux", ("S", "acc")), ("Pair", "d1", "t1"), ("Pair", "d2", "t2"))))))
                (app(comm,assoc)(("aux", "Z"), "a", "b")))))(expr)
    else
        // This would be the same implementation as argmax :: (Nat,Nat) -> (Nat,Nat) -> (Nat,Nat)
        // we can prove it's commutative and associative, Zeno can only prove commutativity
        // HipSpec was unable to prove either commutativity, or associativity
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
    let("gset_merge" ->
        abs(comm,assoc)("a" -> tp(nat -> bool), "b" -> tp(nat -> bool))
           (abs()("x" -> nat)(or("a", "x")("b", "x"))))(expr)


@main def example =
  def check(expr: Term, assumedUncheckedConjectures: List[Normalization] = List.empty) =
    val result = properties.check(expr, assumedUncheckedConjectures, printDeductionDebugInfo = true, printReductionDebugInfo = true)
    val errors = result.showErrors
    if errors.nonEmpty then
      println()
      println(errors)

  // check(ordernat("Z"))
  // println()
  // check(orderlist("Z"))
  // println()
  // check(min("Z"))
  // println()
  // check(max("Z"))
  // println()
  // check(map("Z"))
  // println()
  // check(plus("Z"))
  // println()
  // check(plus(mult("Z")))
  // println()
  // check(bv_succ(bv_plus("Z")))

  // check(max(gcounter_merge("Z")))
  // println()
  // check(max(gcounter_merge(pncounter_merge("Z"))))
  // println()
  // check(plus(max(ordernat(lwwreg_merge("Z")))))
  // println()
  // check(gset_merge("Z"))
  // check(bv_eq(orderbv("Z")))
  // check(bv_eq(bv_max("Z")))
  // check(bv_eq(bvu_eq(ordbvu("Z"))))
  // check(plus(max(lwwreg_merge("Z"))))

  check(plus(max(lwwreg_merge("Z"))),
    List(
      Normalization(app(comm,assoc)(("aux", ("S", "acc")), "a", "b"),
                    cases(app(comm,assoc)(("aux", "acc"), "a", "b"))
                        (("Pair", "d", "t") -> ("Pair", "d", ("S", "t"))),
                    Symbol("aux"),
                    Set(Symbol("acc"), Symbol("a"), Symbol("b")),
                    false)
    ))
