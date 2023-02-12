package propel

import ast.dsl.*
import ast.dsl.sugar.*
import printing.*
import evaluator.*

def nat_leq[A: TermExpr](expr: A) =
  letrec("nat_leq" -> tp(nat -> (nat -> bool)) ->
    abs(refl, antisym, trans, conn)("a" -> nat, "b" -> nat)(let("tuple" -> ("Tuple", "a", "b"))(cases("tuple")(
      ("Tuple", ("S", "x"), ("S", "y")) -> app(refl, antisym, trans, conn)("nat_leq", "x", "y"),
      ("Tuple", "Z", "_") -> True,
      "_" -> False))))(
    expr)

def lnat_leq[A: TermExpr](expr: A) =
  letrec("lnat_leq" -> tp(list(nat) -> (list(nat) -> bool)) ->
    abs(refl, antisym, trans, conn)("a" -> list(nat), "b" -> list(nat))(let("tuple" -> ("Tuple", "a", "b"))(cases("tuple")(
      ("Tuple", ("Cons", ("S", "x"), "xs"), ("Cons", ("S", "y"), "ys")) ->
        app(refl, antisym, trans, conn)("lnat_leq", ("Cons", "x", "xs"), ("Cons", "y", "ys")),
      ("Tuple", ("Cons", "Z", "xs"), ("Cons", "Z", "ys")) ->
        app(refl, antisym, trans, conn)("lnat_leq", "xs", "ys"),
      ("Tuple", ("Cons", "Z", "xs"), ("Cons", "_", "_")) ->
        True,
      ("Tuple", "Nil", "_") ->
        True,
      "_" ->
        False))))(
    expr)

def nat_min[A: TermExpr](expr: A) =
  letrec("min" -> tp(nat -> (nat -> nat)) ->
    abs(assoc, comm, idem)("a" -> nat, "b" -> nat)(cases("Tuple", "a", "b")(
      ("Tuple", ("S", "a"), ("S", "b")) -> ("S", app(assoc, comm, idem)("min", "a", "b")),
      "_" -> "Z")))(
    expr)

def list_map[A: TermExpr](expr: A) =
  letrec("list_map" -> forall("T")(("T" -> ("T" -> "T")) -> (list("T") -> (list("T") -> list("T")))) ->
    tpabs("T")(abs("f" -> tp("T" -> ("T" -> "T")))(abs(assoc, comm, idem)("a" -> list("T"), "b" -> list("T"))(cases("Tuple", "a", "b")(
      ("Tuple", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
        ("Cons", app(assoc, comm, idem)("f", "x", "y"), app(assoc, comm, idem)((tpapp("list_map")(tp("T")), "f"), "xs", "ys")),
      "_" ->
        "Nil")))))(
    expr)

def bv_leq[A: TermExpr](expr: A) =
  letrec("bv_leq" -> tp(bv -> tp(bv -> bool)) ->
    abs(refl, antisym, trans, conn)("a" -> bv, "b" -> bv)(cases("Pair", "a", "b")(
      ("Pair", "BZ", "_") -> True,
      ("Pair", "_", "BZ") -> False,
      ("Pair", ("B0", "a"), ("B0", "b")) -> app(refl, antisym, trans, conn)("bv_leq", "a", "b"),
      ("Pair", ("B0", "a"), ("B1", "b")) -> app(refl, antisym, trans, conn)("bv_leq", "a", "b"),
      ("Pair", ("B1", "a"), ("B0", "b")) -> `and`(app(refl, antisym, trans, conn)("bv_leq", "a", "b"))
                                                 (`not`(app(refl, sym, antisym, trans)("bv_eq", "a", "b"))),
      ("Pair", ("B1", "a"), ("B1", "b")) -> app(refl, antisym, trans, conn)("bv_leq", "a", "b"))))(
    expr)

def bvu_eq[A: TermExpr](expr: A) =
  let("bvu_eq" ->
    abs(refl, sym, antisym, trans)("a" -> bvu, "b" -> bvu)(cases("Pair", "a", "b")(
      ("Pair", "BZ", "BZ") -> True,
      ("Pair", ("B1", "bva"), ("B1", "bvb")) -> app(refl, sym, antisym, trans)("bv_eq", "bva", "bvb"),
      ("Pair", "_1", "_2") -> False)))(
    expr)

def bvu_leq[A: TermExpr](expr: A) =
  letrec("bvu_leq" -> tp(bvu -> tp(bvu -> bool)) ->
    abs(refl, antisym, trans, conn)("a" -> bvu, "b" -> bvu)(cases("Pair", "a", "b")(
      ("Pair", "BZ", "_") -> True,
      ("Pair", "_", "BZ") -> False,
      ("Pair", ("B1", "BZ"), ("B1", "_")) -> True,
      ("Pair", ("B1", "_"), ("B1", "BZ")) -> False,
      ("Pair", ("B1", ("B0", "a")), ("B1", ("B1", "b"))) -> False,
      ("Pair", ("B1", ("B1", "a")), ("B1", ("B0", "b"))) -> True,
      ("Pair", ("B1", ("B0", "a")), ("B1", ("B0", "b"))) ->
        app(refl, antisym, trans, conn)("bvu_leq", ("B1", "a"), ("B1", "b")),
      ("Pair", ("B1", ("B1", "a")), ("B1", ("B1", "b"))) ->
        app(refl, antisym, trans, conn)("bvu_leq", ("B1", "a"), ("B1", "b")))))(
    expr)

def lwwreg = dt("LWWReg", nat, nat)

def nat_lwwreg_alt1[A: TermExpr](expr: A) =
  let("nat_lwwreg_alt1" ->
    abs(assoc, comm, idem)("a" -> lwwreg, "b" -> lwwreg)(
      let(("Tuple", ("LWWReg", "d1", "t1"), ("LWWReg", "d2", "t2")) -> ("Tuple", "a", "b"))(
        `if`(app(refl, antisym, trans, conn)("nat_leq", "t1", "t2"))
            (`if`(app(refl, antisym, trans, conn)("nat_leq", "t2", "t1"))
                 ("LWWReg", app(comm, assoc, idem, sel)("nat_max", "d1", "d2"), "t1")
                 ("LWWReg", "d2", "t2"))
            ("LWWReg", "d1", "t1"))))(
    expr)

def nat_lwwreg_alt2[A: TermExpr](expr: A) =
  letrec("nat_lwwreg_alt2" -> tp(lwwreg -> (lwwreg -> lwwreg)) ->
    abs(assoc, comm, idem)("a" -> lwwreg, "b" -> lwwreg)(cases("Tuple", "a", "b")(
      ("Tuple", ("LWWReg", "d1", "Z"), ("LWWReg", "d2", "Z")) ->
        ("LWWReg", app(comm, assoc, idem, sel)("nat_max", "d1", "d2"), "Z"),
      ("Tuple", ("LWWReg", "d1", ("S","t1")), ("LWWReg", "d2", "Z")) ->
        ("LWWReg", "d1", ("S", "t1")),
      ("Tuple", ("LWWReg", "d1", "Z"), ("LWWReg", "d2", ("S","t2"))) ->
        ("LWWReg", "d2", ("S", "t2")),
      ("Tuple", ("LWWReg", "d1", ("S", "t1")), ("LWWReg", "d2", ("S", "t2"))) ->
        let(("LWWReg", "d", "t") -> app(comm, assoc, idem)("nat_lwwreg_alt2", ("LWWReg", "d1", "t1"), ("LWWReg", "d2", "t2")))(
          "LWWReg", "d", ("S", "t")))))(
    expr)

def nat_lwwreg_alt3[A: TermExpr](expr: A) =
  let("nat_lwwreg_alt3" ->
    abs(assoc, comm, idem)("a" -> lwwreg, "b" -> lwwreg)(
      letrec("aux" -> tp(nat -> (lwwreg -> (lwwreg -> lwwreg))) ->
        abs("acc" -> nat, "a" -> lwwreg, "b" -> lwwreg)(cases("Tuple", "a", "b")(
          ("Tuple", ("LWWReg", "d1", "Z"), ("LWWReg", "d2", "Z")) ->
            ("LWWReg", app(comm, assoc, idem, sel)("nat_max", "d1", "d2"), "acc"),
          ("Tuple", ("LWWReg", "d1", ("S","t1")), ("LWWReg", "d2", "Z")) ->
            ("LWWReg", "d1", app(comm, assoc)("nat_add2p", "acc", ("S", "t1"))),
          ("Tuple", ("LWWReg", "d1", "Z"), ("LWWReg", "d2", ("S","t2"))) ->
            ("LWWReg", "d2", app(comm, assoc)("nat_add2p", "acc", ("S", "t2"))),
          ("Tuple", ("LWWReg", "d1", ("S", "t1")), ("LWWReg", "d2", ("S", "t2"))) ->
            ("aux", ("S", "acc"), ("LWWReg", "d1", "t1"), ("LWWReg", "d2", "t2")))))(
        ("aux", "Z", "a", "b"))))(
    expr)

def examples = List(
  "nat_leq" -> nat_leq("Unit"),
  "lnat_leq" -> lnat_leq("Unit"),
  "nat_min" -> nat_min("Unit"),
  "list_map" -> list_map("Unit"),
  "bv_leq" -> bv_eq(bv_leq("Unit")),
  "bvu_eq" -> bv_eq(bvu_eq("Unit")),
  "bvu_leq" -> bvu_leq("Unit"),
  "nat_lwwreg_alt1" -> nat_max(nat_leq(nat_lwwreg_alt1("Unit"))),
  "nat_lwwreg_alt2" -> nat_max(nat_lwwreg_alt2("Unit")),
  "nat_lwwreg_alt3" -> nat_max(nat_add2p(nat_lwwreg_alt3("Unit"))))

@main def example(example: String) =
  val ex = examples.toMap
  val errors = properties.check(ex(example), printDeductionDebugInfo = false, printReductionDebugInfo = false).showErrors
  if errors.nonEmpty then
    println(errors)
  else
    println(s"✔ checked: $example")
