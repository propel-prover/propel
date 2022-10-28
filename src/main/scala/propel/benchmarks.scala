package propel

import ast.dsl.*
import ast.dsl.sugar.*
import printing.*
import evaluator.*


def nat_max[A: TermExpr](expr: A) =
  letrec("nat_max" -> tp(nat -> (nat -> nat)) ->
    abs(comm, assoc, idem, sel)("x" -> nat, "y" -> nat)(cases("Tuple", "x", "y")(
      ("Tuple", "Z", "y") -> "y",
      ("Tuple", "x", "Z") -> "x",
      ("Tuple", ("S", "x"), ("S", "y")) -> ("S", app(comm, assoc, idem, sel)("nat_max", "x", "y")))))(
    expr)

def bv_eq[A: TermExpr](expr: A) =
  letrec("bv_eq" -> tp(bv -> tp(bv -> bool)) ->
    abs(refl, sym, antisym, trans)("x" -> bv, "y" -> bv)(cases("Tuple", "x", "y")(
      ("Tuple", "BZ", "BZ") -> True,
      ("Tuple", ("B0", "x"), ("B0", "y")) -> app(refl, sym, antisym, trans)("bv_eq", "x", "y"),
      ("Tuple", ("B1", "x"), ("B1", "y")) -> app(refl, sym, antisym, trans)("bv_eq", "x", "y"),
      ("_") -> False)))(
    expr)

def bv_max[A: TermExpr](expr: A) =
  letrec("bv_max" -> tp(bv -> (bv -> bv)) ->
    abs(assoc, comm, idem, sel)("x" -> bv, "y" -> bv)(cases("Tuple", "x", "y")(
      ("Tuple", "BZ", "y") -> "y",
      ("Tuple", "x", "BZ") -> "x",
      ("Tuple", ("B0", "x"), ("B0", "y")) -> ("B0", app(assoc, comm, idem, sel)("bv_max", "x", "y")),
      ("Tuple", ("B1", "x"), ("B1", "y")) -> ("B1", app(assoc, comm, idem, sel)("bv_max", "x", "y")),
      ("Tuple", ("B0", "x"), ("B1", "y")) ->
        `if`(app(refl, sym, antisym, trans)("bv_eq", app(assoc, comm, idem, sel)("bv_max", "x", "y"), "y"))
          ("B1", "y")
          ("B0", "x"),
      ("Tuple", ("B1", "x"), ("B0", "y")) ->
        `if`(app(refl, sym, antisym, trans)("bv_eq", app(assoc, comm, idem, sel)("bv_max", "x", "y"), "x"))
          ("B1", "x")
          ("B0", "y"))))(
    expr)

def natlist_gcounter[A: TermExpr](expr: A) =
  letrec("natlist_gcounter" -> tp(list(nat) -> (list(nat) -> list(nat))) ->
    abs(comm, assoc, idem)("x" -> list(nat), "y" -> list(nat))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
        ("Cons", app(comm, assoc, idem, sel)("nat_max", "x", "y"), app(comm, assoc, idem)("natlist_gcounter", "xs", "ys")))))(
    expr)

def bvlist_gcounter[A: TermExpr](expr: A) =
  letrec("bvlist_gcounter" -> tp(list(bv) -> (list(bv) -> list(bv))) ->
    abs(comm, assoc, idem)("x" -> list(bv), "y" -> list(bv))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
        ("Cons", app(comm, assoc, idem, sel)("bv_max", "x", "y"), app(comm, assoc, idem)("bvlist_gcounter", "xs", "ys")))))(
    expr)

def natlist_pncounter[A: TermExpr](expr: A) =
  let("natlist_pncounter" ->
    abs(comm, assoc, idem)("x" -> dt("PNCounter", list(nat), list(nat)), "y" -> dt("PNCounter", list(nat), list(nat)))(
      let(("Tuple", ("PNCounter", "xn", "xp"), ("PNCounter", "yn", "yp")) -> ("Tuple", "x", "y"))(
        "PNCounter", app(comm, assoc, idem)("natlist_gcounter", "xn", "yn"), app(comm, assoc, idem)("natlist_gcounter", "xp", "yp"))))(
    expr)

def bvlist_pncounter[A: TermExpr](expr: A) =
  let("bvlist_pncounter" ->
    abs(comm, assoc, idem)("x" -> dt("PNCounter", list(bv), list(bv)), "y" -> dt("PNCounter", list(bv), list(bv)))(
      let(("Tuple", ("PNCounter", "xn", "xp"), ("PNCounter", "yn", "yp")) -> ("Tuple", "x", "y"))(
        "PNCounter", app(comm, assoc, idem)("bvlist_gcounter", "xn", "yn"), app(comm, assoc, idem)("bvlist_gcounter", "xp", "yp"))))(
    expr)

def natlist_version_bcounter[A: TermExpr](expr: A) =
  letrec("natlist_version_bcounter" -> tp(list(list(nat)) -> (list(list(nat)) -> list(list(nat)))) ->
    abs(comm, assoc, idem)("x" -> list(list(nat)), "y" -> list(list(nat)))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
        ("Cons", app(comm, assoc, idem)("natlist_gcounter", "x", "y"), app(comm, assoc, idem)("natlist_version_bcounter", "xs", "ys")))))(
    expr)

def bvlist_version_bcounter[A: TermExpr](expr: A) =
  letrec("bvlist_version_bcounter" -> tp(list(list(bv)) -> (list(list(bv)) -> list(list(bv)))) ->
    abs(comm, assoc, idem)("x" -> list(list(bv)), "y" -> list(list(bv)))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
        ("Cons", app(comm, assoc, idem)("bvlist_gcounter", "x", "y"), app(comm, assoc, idem)("bvlist_version_bcounter", "xs", "ys")))))(
    expr)

def natlist_bcounter[A: TermExpr](expr: A) =
  let("natlist_bcounter" ->
    abs(comm, assoc, idem)(
        "x" -> dt("BCounter", dt("PNCounter", list(nat), list(nat)), list(list(nat))),
        "y" -> dt("BCounter", dt("PNCounter", list(nat), list(nat)), list(list(nat))))(
      let(("Tuple", ("BCounter", "xpn", "xv"), ("BCounter", "ypn", "yv")) -> ("Tuple", "x", "y"))(
        "BCounter", app(comm, assoc, idem)("natlist_pncounter", "xpn", "ypn"), app(comm, assoc, idem)("natlist_version_bcounter", "xv", "yv"))))(
    expr)

def bvlist_bcounter[A: TermExpr](expr: A) =
  let("bvlist_bcounter" ->
    abs(comm, assoc, idem)(
        "x" -> dt("BCounter", dt("PNCounter", list(bv), list(bv)), list(list(bv))),
        "y" -> dt("BCounter", dt("PNCounter", list(bv), list(bv)), list(list(bv))))(
      let(("Tuple", ("BCounter", "xpn", "xv"), ("BCounter", "ypn", "yv")) -> ("Tuple", "x", "y"))(
        "BCounter", app(comm, assoc, idem)("bvlist_pncounter", "xpn", "ypn"), app(comm, assoc, idem)("bvlist_version_bcounter", "xv", "yv"))))(
    expr)

def nat_lwwreg[A: TermExpr](expr: A) =
  letrec("nat_lwwreg" -> tp(dt("LWWReg", nat, nat) -> (dt("LWWReg", nat, nat) -> dt("LWWReg", nat, nat))) ->
    abs(comm, assoc, idem)("x" -> dt("LWWReg", nat, nat), "y" -> dt("LWWReg", nat, nat))(cases("Tuple", "x", "y")(
      ("Tuple", ("LWWReg", "xd", "Z"), ("LWWReg", "yd", "Z")) -> ("LWWReg", app(comm, assoc, idem, sel)("nat_max", "xd", "yd"), "Z"),
      ("Tuple", ("LWWReg", "xd", "Z"), ("LWWReg", "yd", "yt")) -> ("LWWReg", "yd", "yt"),
      ("Tuple", ("LWWReg", "xd", "xt"), ("LWWReg", "yd", "Z")) -> ("LWWReg", "xd", "xt"),
      ("Tuple", ("LWWReg", "xd", ("S", "xt")), ("LWWReg", "yd", ("S", "yt"))) ->
        let(("LWWReg", "d", "t") -> app(comm, assoc, idem)("nat_lwwreg", ("LWWReg", "xd", "xt"), ("LWWReg", "yd", "yt")))(
          ("LWWReg", "d", ("S", "t"))))))(
    expr)

def bv_lwwreg[A: TermExpr](expr: A) =
  let("bv_lwwreg" ->
    abs(comm, assoc, idem)("x" -> dt("LWWReg", bv, bv), "y" -> dt("LWWReg", bv, bv))(
      let(("Tuple", ("LWWReg", "xd", "xt"), ("LWWReg", "yd", "yt")) -> ("Tuple", "x", "y"))(
        `if`(app(refl, sym, antisym, trans)("bv_eq", "xt", "yt"))
            ("LWWReg", app(comm, assoc, idem, sel)("bv_max", "xd", "yd"), "xt")
            (`if`(app(refl, sym, antisym, trans)("bv_eq", app(comm, assoc, idem, sel)("bv_max", "xt", "yt"), "xt"))
                 ("LWWReg", "xd", "xt")
                 ("LWWReg", "yd", "yt")))))(
    expr)

def gset[A: TermExpr](expr: A) =
  let("gset" ->
    abs(comm, assoc, idem)("x" -> tp(nat -> bool), "y" -> tp(nat -> bool))(
      abs("n" -> nat)(or("x", "n")("y", "n"))))(expr)

def orset[A: TermExpr](expr: A) =
  let("orset" ->
    abs(comm, assoc, idem)("x" -> tp(bool -> (nat -> option(list(nat)))), "y" -> tp(bool -> (nat -> option(list(nat)))))(
      abs("b" -> bool, "n" -> nat)(cases("x", "b", "n")(
        "None" -> ("y", "b", "n"),
        ("Some", "xl") -> cases("y", "b", "n")(
          "None" -> ("Some", "xl"),
          ("Some", "yl") -> ("Some", app(comm, assoc, idem)("natlist_gcounter", "xl", "yl")))))))(
    expr)

def twopset[A: TermExpr](expr: A) =
  let("twopset" ->
    abs(comm, assoc, idem)("x" -> tp(bool -> (nat -> bool)), "y" -> tp(bool -> (nat -> bool)))(
      abs("b" -> bool, "n" -> nat)(or("x", "b", "n")("y", "b", "n"))))(expr)


val benchmarks = Map(
  "natlist_gcounter" -> nat_max(natlist_gcounter("Unit")),
  "bvlist_gcounter" -> bv_eq(bv_max(bvlist_gcounter("Unit"))),
  "natlist_bcounter" -> nat_max(natlist_gcounter(natlist_pncounter(natlist_version_bcounter(natlist_bcounter("Unit"))))),
  "bvlist_bcounter" -> bv_eq(bv_max(bvlist_gcounter(bvlist_pncounter(bvlist_version_bcounter(bvlist_bcounter("Unit")))))),
  "nat_lwwreg" -> nat_max(nat_lwwreg("Unit")),
  "bv_lwwreg" -> bv_eq(bv_max(bv_lwwreg("Unit"))),
  "gset" -> gset("Unit"),
  "orset" -> nat_max(natlist_gcounter(orset("Unit"))),
  "twopset" -> twopset("Unit"))


@main def benchmark(benchmark: String) =
  val errors = properties.check(benchmarks(benchmark), printDeductionDebugInfo = false, printReductionDebugInfo = false).showErrors
  if errors.nonEmpty then
    println(errors)
