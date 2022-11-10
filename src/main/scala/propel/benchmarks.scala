package propel

import ast.dsl.*
import ast.dsl.sugar.*
import printing.*
import evaluator.*


def nat_add2p[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc)) =
  letrec("nat_add2p" -> tp(nat -> (nat -> nat)) ->
    abs(properties*)("x" -> nat, "y" -> nat)(cases("x")(
      "Z" -> "y",
      ("S", "x") -> ("S", app(comm, assoc)("nat_add2p", "x", "y")))))(
    expr)

def nat_add2p_acc[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc)) =
  let("nat_add2p_acc" ->
    abs(properties*)("x" -> nat, "y" -> nat)(
      letrec("nat_add2p_acc" -> tp(nat -> (nat -> (nat -> nat))) ->
        abs("acc" -> nat, "x" -> nat, "y" -> nat)(cases("Tuple", "x", "y")(
          ("Tuple", "Z", "Z") -> "acc",
          ("Tuple", ("S", "x"), "y") -> ("nat_add2p_acc", ("S", "acc"), "x", "y"),
          ("Tuple", "Z", ("S", "y")) -> ("nat_add2p_acc", ("S", "acc"), "Z", "y"))))(
        "nat_add2p_acc", "Z", "x", "y")))(
    expr)

def nat_add3p[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc)) =
  letrec("nat_add3p" -> tp(nat -> (nat -> nat)) ->
    abs(properties*)("x" -> nat, "y" -> nat)(cases("Tuple", "x", "y")(
      ("Tuple", "Z", "y") -> "y",
      ("Tuple", "x", "Z") -> "x",
      ("Tuple", ("S", "x"), ("S", "y")) -> ("S", ("S", app(comm, assoc)("nat_add3p", "x", "y"))))))(
    expr)

def nat_add3p_acc[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc)) =
  let("nat_add3p_acc" ->
    abs(properties*)("x" -> nat, "y" -> nat)(
      letrec("nat_add3p_acc" -> tp(nat -> (nat -> (nat -> nat))) ->
        abs("acc" -> nat, "x" -> nat, "y" -> nat)(cases("Tuple", "x", "y")(
          ("Tuple", "Z", "Z") -> "acc",
          ("Tuple", ("S", "x"), "Z") -> ("nat_add3p_acc", ("S", "acc"), "x", "Z"),
          ("Tuple", "Z", ("S", "y")) -> ("nat_add3p_acc", ("S", "acc"), "Z", "y"),
          ("Tuple", ("S", "x"), ("S", "y")) -> ("nat_add3p_acc", ("S", ("S", "acc")), "Z", "y"))))(
        "nat_add3p_acc", "Z", "x", "y")))(
    expr)

def nat_mult2p[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc)) =
  letrec("nat_mult2p" -> tp(nat -> (nat -> nat)) ->
    abs(properties*)("x" -> nat, "y" -> nat)(cases("x")(
      "Z" -> "Z",
      ("S", "x") -> app(comm, assoc)("nat_add2p", "y", app(comm, assoc)("nat_mult2p", "x", "y")))))(
    expr)

def nat_mult2p_acc[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc)) =
  let("nat_mult2p_acc" ->
    abs(properties*)("x" -> nat, "y" -> nat)(
      letrec("nat_mult2p_acc" -> tp(nat -> (nat -> (nat -> nat))) ->
        abs("acc" -> nat, "x" -> nat, "y" -> nat)(cases("x")(
          "Z" -> "acc",
          ("S", "x") -> ("nat_mult2p_acc", app(comm, assoc)("nat_add2p", "y", "acc"), "x", "y"))))(
        "nat_mult2p_acc", "Z", "x", "y")))(
    expr)

def nat_mult3p[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc)) =
  letrec("nat_mult3p" -> tp(nat -> (nat -> nat)) ->
    abs(properties*)("x" -> nat, "y" -> nat)(cases("Tuple", "x", "y")(
      ("Tuple", "Z", "y") -> "Z",
      ("Tuple", "x", "Z") -> "Z",
      ("Tuple", ("S", "x"), ("S", "y")) ->
        app(comm, assoc)("nat_add3p", app(comm, assoc)("nat_add3p", "x", "y"), app(comm, assoc)("nat_mult3p", "x", "y")))))(
    expr)

def bv_succ[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq()) =
  letrec("bv_succ" -> tp(bv -> bv) ->
    abs(properties*)("x" -> bv)(cases("x")(
      ("BZ") -> ("B1", "BZ"),
      ("B0", "x") -> ("B1", "x"),
      ("B1", "x") -> ("B0", ("bv_succ", "x")))))(
    expr)

def bv_add[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc)) =
  letrec("bv_add" -> tp(bv -> (bv -> bv)) ->
    abs(properties*)("x" -> bv, "y" -> bv)(cases("Tuple", "x", "y")(
      ("Tuple", "BZ", "BZ") -> "BZ",
      ("Tuple", "BZ", ("B0", "y")) -> ("B0", "y"),
      ("Tuple", "BZ", ("B1", "y")) -> ("B1", "y"),
      ("Tuple", ("B0", "x"), "BZ") -> ("B0", "x"),
      ("Tuple", ("B1", "x"), "BZ") -> ("B1", "x"),
      ("Tuple", ("B0", "x"), ("B0", "y")) -> ("B0", app(comm, assoc)("bv_add", "x", "y")),
      ("Tuple", ("B0", "x"), ("B1", "y")) -> ("B1", app(comm, assoc)("bv_add", "x", "y")),
      ("Tuple", ("B1", "x"), ("B0", "y")) -> ("B1", app(comm, assoc)("bv_add", "x", "y")),
      ("Tuple", ("B1", "x"), ("B1", "y")) -> ("B0", ("bv_succ", app(comm, assoc)("bv_add", "x", "y"))))))(
    expr)

def lnat_append[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(assoc)) =
  letrec("lnat_append" -> tp(list(nat) -> (list(nat) -> list(nat))) ->
    abs(properties*)("x" -> list(nat), "y" -> list(nat))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), "y") -> ("Cons", "x", app(assoc)("lnat_append", "xs", "y")))))(
    expr)

def lbv_append[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(assoc)) =
  letrec("lbv_append" -> tp(list(bv) -> (list(bv) -> list(bv))) ->
    abs(properties*)("x" -> list(bv), "y" -> list(bv))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), "y") -> ("Cons", "x", app(assoc)("lbv_append", "xs", "y")))))(
    expr)

def llnat_append[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(assoc)) =
  letrec("llnat_append" -> tp(list(list(nat)) -> (list(list(nat)) -> list(list(nat)))) ->
    abs(properties*)("x" -> list(list(nat)), "y" -> list(list(nat)))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), "y") -> ("Cons", "x", app(assoc)("llnat_append", "xs", "y")))))(
    expr)

def llbv_append[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(assoc)) =
  letrec("llbv_append" -> tp(list(list(bv)) -> (list(list(bv)) -> list(list(bv)))) ->
    abs(properties*)("x" -> list(list(bv)), "y" -> list(list(bv)))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), "y") -> ("Cons", "x", app(assoc)("llbv_append", "xs", "y")))))(
    expr)

def nat_max[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem, sel)) =
  letrec("nat_max" -> tp(nat -> (nat -> nat)) ->
    abs(properties*)("x" -> nat, "y" -> nat)(cases("Tuple", "x", "y")(
      ("Tuple", "Z", "y") -> "y",
      ("Tuple", "x", "Z") -> "x",
      ("Tuple", ("S", "x"), ("S", "y")) -> ("S", app(comm, assoc, idem, sel)("nat_max", "x", "y")))))(
    expr)

def nat_max_acc[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem, sel)) =
  let("nat_max_acc" ->
    abs(properties*)("x" -> nat, "y" -> nat)(
      letrec("nat_max_acc" -> tp(nat -> (nat -> (nat -> nat))) ->
        abs("acc" -> nat, "x" -> nat, "y" -> nat)(cases("Tuple", "x", "y")(
          ("Tuple", "Z", "Z") -> "acc",
          ("Tuple", ("S", "x"), "Z") -> ("nat_add2p", "acc", ("S", "x")),
          ("Tuple", "Z", ("S", "y")) -> ("nat_add2p", "acc", ("S", "y")),
          ("Tuple", ("S", "x"), ("S", "y")) -> ("nat_max_acc", ("S", "acc"), "x", "y"))))(
        "nat_max_acc", "Z", "x", "y")))(
    expr)

def bv_eq[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(refl, sym, antisym, trans)) =
  letrec("bv_eq" -> tp(bv -> tp(bv -> bool)) ->
    abs(properties*)("x" -> bv, "y" -> bv)(cases("Tuple", "x", "y")(
      ("Tuple", "BZ", "BZ") -> True,
      ("Tuple", ("B0", "x"), ("B0", "y")) -> app(refl, sym, antisym, trans)("bv_eq", "x", "y"),
      ("Tuple", ("B1", "x"), ("B1", "y")) -> app(refl, sym, antisym, trans)("bv_eq", "x", "y"),
      ("_") -> False)))(
    expr)

def bv_max[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(assoc, comm, idem, sel)) =
  letrec("bv_max" -> tp(bv -> (bv -> bv)) ->
    abs(properties*)("x" -> bv, "y" -> bv)(cases("Tuple", "x", "y")(
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

def natlist_gcounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  letrec("natlist_gcounter" -> tp(list(nat) -> (list(nat) -> list(nat))) ->
    abs(properties*)("x" -> list(nat), "y" -> list(nat))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
        ("Cons", app(comm, assoc, idem, sel)("nat_max", "x", "y"), app(comm, assoc, idem)("natlist_gcounter", "xs", "ys")))))(
    expr)

def bvlist_gcounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  letrec("bvlist_gcounter" -> tp(list(bv) -> (list(bv) -> list(bv))) ->
    abs(properties*)("x" -> list(bv), "y" -> list(bv))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
        ("Cons", app(comm, assoc, idem, sel)("bv_max", "x", "y"), app(comm, assoc, idem)("bvlist_gcounter", "xs", "ys")))))(
    expr)

def natlist_pncounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("natlist_pncounter" ->
    abs(properties*)("x" -> dt("PNCounter", list(nat), list(nat)), "y" -> dt("PNCounter", list(nat), list(nat)))(
      let(("Tuple", ("PNCounter", "xn", "xp"), ("PNCounter", "yn", "yp")) -> ("Tuple", "x", "y"))(
        "PNCounter", app(comm, assoc, idem)("natlist_gcounter", "xn", "yn"), app(comm, assoc, idem)("natlist_gcounter", "xp", "yp"))))(
    expr)

def bvlist_pncounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("bvlist_pncounter" ->
    abs(properties*)("x" -> dt("PNCounter", list(bv), list(bv)), "y" -> dt("PNCounter", list(bv), list(bv)))(
      let(("Tuple", ("PNCounter", "xn", "xp"), ("PNCounter", "yn", "yp")) -> ("Tuple", "x", "y"))(
        "PNCounter", app(comm, assoc, idem)("bvlist_gcounter", "xn", "yn"), app(comm, assoc, idem)("bvlist_gcounter", "xp", "yp"))))(
    expr)

def natlist_version_bcounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  letrec("natlist_version_bcounter" -> tp(list(list(nat)) -> (list(list(nat)) -> list(list(nat)))) ->
    abs(properties*)("x" -> list(list(nat)), "y" -> list(list(nat)))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
        ("Cons", app(comm, assoc, idem)("natlist_gcounter", "x", "y"), app(comm, assoc, idem)("natlist_version_bcounter", "xs", "ys")))))(
    expr)

def bvlist_version_bcounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  letrec("bvlist_version_bcounter" -> tp(list(list(bv)) -> (list(list(bv)) -> list(list(bv)))) ->
    abs(properties*)("x" -> list(list(bv)), "y" -> list(list(bv)))(cases("Tuple", "x", "y")(
      ("Tuple", "Nil", "y") -> "y",
      ("Tuple", "x", "Nil") -> "x",
      ("Tuple", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
        ("Cons", app(comm, assoc, idem)("bvlist_gcounter", "x", "y"), app(comm, assoc, idem)("bvlist_version_bcounter", "xs", "ys")))))(
    expr)

def natlist_bcounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("natlist_bcounter" ->
    abs(properties*)(
        "x" -> dt("BCounter", dt("PNCounter", list(nat), list(nat)), list(list(nat))),
        "y" -> dt("BCounter", dt("PNCounter", list(nat), list(nat)), list(list(nat))))(
      let(("Tuple", ("BCounter", "xpn", "xv"), ("BCounter", "ypn", "yv")) -> ("Tuple", "x", "y"))(
        "BCounter", app(comm, assoc, idem)("natlist_pncounter", "xpn", "ypn"), app(comm, assoc, idem)("natlist_version_bcounter", "xv", "yv"))))(
    expr)

def bvlist_bcounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("bvlist_bcounter" ->
    abs(properties*)(
        "x" -> dt("BCounter", dt("PNCounter", list(bv), list(bv)), list(list(bv))),
        "y" -> dt("BCounter", dt("PNCounter", list(bv), list(bv)), list(list(bv))))(
      let(("Tuple", ("BCounter", "xpn", "xv"), ("BCounter", "ypn", "yv")) -> ("Tuple", "x", "y"))(
        "BCounter", app(comm, assoc, idem)("bvlist_pncounter", "xpn", "ypn"), app(comm, assoc, idem)("bvlist_version_bcounter", "xv", "yv"))))(
    expr)

def natmap_gcounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("natmap_gcounter" ->
    abs(properties*)("x" -> tp(nat -> option(nat)), "y" -> tp(nat -> option(nat)))(
      abs("n" -> nat)(cases("x", "n")(
        "None" -> ("y", "n"),
        ("Some", "x") -> cases("y", "n")(
          "None" -> ("Some", "x"),
          ("Some", "y") -> ("Some", app(comm, assoc, idem, sel)("nat_max", "x", "y")))))))(
    expr)

def bvmap_gcounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("bvmap_gcounter" ->
    abs(properties*)("x" -> tp(nat -> option(bv)), "y" -> tp(nat -> option(bv)))(
      abs("n" -> nat)(cases("x", "n")(
        "None" -> ("y", "n"),
        ("Some", "x") -> cases("y", "n")(
          "None" -> ("Some", "x"),
          ("Some", "y") -> ("Some", app(comm, assoc, idem, sel)("bv_max", "x", "y")))))))(
    expr)

def natmap_pncounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("natmap_pncounter" ->
    abs(properties*)("x" -> tp(dt("Tuple", bool, nat) -> option(nat)), "y" -> tp(dt("Tuple", bool, nat) -> option(nat)))(
      abs("n" -> dt("Tuple", bool, nat))(cases("x", "n")(
        "None" -> ("y", "n"),
        ("Some", "x") -> cases("y", "n")(
          "None" -> ("Some", "x"),
          ("Some", "y") -> ("Some", app(comm, assoc, idem, sel)("nat_max", "x", "y")))))))(
    expr)

def bvmap_pncounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("bvmap_pncounter" ->
    abs(properties*)("x" -> tp(dt("Tuple", bool, nat) -> option(bv)), "y" -> tp(dt("Tuple", bool, nat) -> option(bv)))(
      abs("n" -> dt("Tuple", bool, nat))(cases("x", "n")(
        "None" -> ("y", "n"),
        ("Some", "x") -> cases("y", "n")(
          "None" -> ("Some", "x"),
          ("Some", "y") -> ("Some", app(comm, assoc, idem, sel)("bv_max", "x", "y")))))))(
    expr)

def natmap_bcounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("natmap_bcounter" ->
    abs(properties*)(
        "x" -> tp(dt("Tuple", dt("Tuple", bool, nat), dt("Tuple", bool, nat)) -> option(nat)),
        "y" -> tp(dt("Tuple", dt("Tuple", bool, nat), dt("Tuple", bool, nat)) -> option(nat)))(
      abs("n" -> dt("Tuple", dt("Tuple", bool, nat), dt("Tuple", bool, nat)))(cases("x", "n")(
        "None" -> ("y", "n"),
        ("Some", "x") -> cases("y", "n")(
          "None" -> ("Some", "x"),
          ("Some", "y") -> ("Some", app(comm, assoc, idem, sel)("nat_max", "x", "y")))))))(
    expr)

def bvmap_bcounter[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("bvmap_bcounter" ->
    abs(properties*)(
        "x" -> tp(dt("Tuple", dt("Tuple", bool, nat), dt("Tuple", bool, nat)) -> option(bv)),
        "y" -> tp(dt("Tuple", dt("Tuple", bool, nat), dt("Tuple", bool, nat)) -> option(bv)))(
      abs("n" -> dt("Tuple", dt("Tuple", bool, nat), dt("Tuple", bool, nat)))(cases("x", "n")(
        "None" -> ("y", "n"),
        ("Some", "x") -> cases("y", "n")(
          "None" -> ("Some", "x"),
          ("Some", "y") -> ("Some", app(comm, assoc, idem, sel)("bv_max", "x", "y")))))))(
    expr)

def nat_lwwreg[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  letrec("nat_lwwreg" -> tp(dt("LWWReg", nat, nat) -> (dt("LWWReg", nat, nat) -> dt("LWWReg", nat, nat))) ->
    abs(properties*)("x" -> dt("LWWReg", nat, nat), "y" -> dt("LWWReg", nat, nat))(cases("Tuple", "x", "y")(
      ("Tuple", ("LWWReg", "xd", "Z"), ("LWWReg", "yd", "Z")) -> ("LWWReg", app(comm, assoc, idem, sel)("nat_max", "xd", "yd"), "Z"),
      ("Tuple", ("LWWReg", "xd", "Z"), ("LWWReg", "yd", "yt")) -> ("LWWReg", "yd", "yt"),
      ("Tuple", ("LWWReg", "xd", "xt"), ("LWWReg", "yd", "Z")) -> ("LWWReg", "xd", "xt"),
      ("Tuple", ("LWWReg", "xd", ("S", "xt")), ("LWWReg", "yd", ("S", "yt"))) ->
        let(("LWWReg", "d", "t") -> app(comm, assoc, idem)("nat_lwwreg", ("LWWReg", "xd", "xt"), ("LWWReg", "yd", "yt")))(
          ("LWWReg", "d", ("S", "t"))))))(
    expr)

def nat_lwwreg_acc[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("nat_lwwreg_acc" ->
    abs(properties*)("x" -> dt("LWWReg", nat, nat), "y" -> dt("LWWReg", nat, nat))(
      letrec("nat_lwwreg_acc" -> tp(nat -> (dt("LWWReg", nat, nat) -> (dt("LWWReg", nat, nat) -> dt("LWWReg", nat, nat)))) ->
        abs("acc" -> nat, "x" -> dt("LWWReg", nat, nat), "y" -> dt("LWWReg", nat, nat))(cases("Tuple", "x", "y")(
          ("Tuple", ("LWWReg", "xd", "Z"), ("LWWReg", "yd", "Z")) -> ("LWWReg", app(comm, assoc, idem, sel)("nat_max", "xd", "yd"), "acc"),
          ("Tuple", ("LWWReg", "xd", "Z"), ("LWWReg", "yd", "yt")) -> ("LWWReg", "yd", app(comm, assoc)("nat_add2p", "yt", "acc")),
          ("Tuple", ("LWWReg", "xd", "xt"), ("LWWReg", "yd", "Z")) -> ("LWWReg", "xd", app(comm, assoc)("nat_add2p", "xt", "acc")),
          ("Tuple", ("LWWReg", "xd", "xt"), ("LWWReg", "yd", "yt")) -> ("nat_lwwreg_acc", ("S", "acc"), ("LWWReg", "xd", "xt"), ("LWWReg", "yd", "yt")))))(
        "nat_lwwreg_acc", "Z", "x", "y")))(
    expr)

def bv_lwwreg[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("bv_lwwreg" ->
    abs(properties*)("x" -> dt("LWWReg", bv, bv), "y" -> dt("LWWReg", bv, bv))(
      let(("Tuple", ("LWWReg", "xd", "xt"), ("LWWReg", "yd", "yt")) -> ("Tuple", "x", "y"))(
        `if`(app(refl, sym, antisym, trans)("bv_eq", "xt", "yt"))
            ("LWWReg", app(comm, assoc, idem, sel)("bv_max", "xd", "yd"), "xt")
            (`if`(app(refl, sym, antisym, trans)("bv_eq", app(comm, assoc, idem, sel)("bv_max", "xt", "yt"), "xt"))
                 ("LWWReg", "xd", "xt")
                 ("LWWReg", "yd", "yt")))))(
    expr)

def gset[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("gset" ->
    abs(properties*)("x" -> tp(nat -> bool), "y" -> tp(nat -> bool))(
      abs("n" -> nat)(or("x", "n")("y", "n"))))(expr)

def orset[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("orset" ->
    abs(properties*)("x" -> tp(bool -> (nat -> option(list(nat)))), "y" -> tp(bool -> (nat -> option(list(nat)))))(
      abs("b" -> bool, "n" -> nat)(cases("x", "b", "n")(
        "None" -> ("y", "b", "n"),
        ("Some", "xl") -> cases("y", "b", "n")(
          "None" -> ("Some", "xl"),
          ("Some", "yl") -> ("Some", app(comm, assoc, idem)("natlist_gcounter", "xl", "yl")))))))(
    expr)

def twophaseset[A: TermExpr](expr: A, properties: Seq[ast.Property] = Seq(comm, assoc, idem)) =
  let("twophaseset" ->
    abs(properties*)("x" -> tp(bool -> (nat -> bool)), "y" -> tp(bool -> (nat -> bool)))(
      abs("b" -> bool, "n" -> nat)(or("x", "b", "n")("y", "b", "n"))))(expr)


def benchmarks(properties: Seq[ast.Property] = Seq()) = Map(
  "nat_add2p" -> nat_add2p("Unit", properties),
  "nat_add2p_acc" -> nat_add2p_acc("Unit", properties),
  "nat_add3p" -> nat_add3p("Unit", properties),
  "nat_add3p_acc" -> nat_add3p_acc("Unit", properties),
  "nat_mult2p" -> nat_add2p(nat_mult2p("Unit", properties)),
  "nat_mult2p_acc" -> nat_add2p(nat_mult2p_acc("Unit", properties)),
  "nat_mult3p" -> nat_add3p(nat_mult3p("Unit", properties)),
  "bv_add" -> bv_succ(bv_add("Unit", properties)),
  "lnat_append" -> lnat_append("Unit", properties),
  "lbv_append" -> lbv_append("Unit", properties),
  "llnat_append" -> llnat_append("Unit", properties),
  "llbv_append" -> llbv_append("Unit", properties),
  "nat_max" -> nat_max("Unit", properties),
  "nat_max_acc" -> nat_add2p(nat_max_acc("Unit", properties)),
  "bv_eq" -> bv_eq("Unit", properties),
  "bv_max" -> bv_eq(bv_max("Unit", properties)),
  "natlist_gcounter" -> nat_max(natlist_gcounter("Unit", properties)),
  "bvlist_gcounter" -> bv_eq(bv_max(bvlist_gcounter("Unit", properties))),
  "natlist_pncounter" -> nat_max(natlist_gcounter(natlist_pncounter("Unit", properties))),
  "bvlist_pncounter" -> bv_eq(bv_max(bvlist_gcounter(bvlist_pncounter("Unit", properties)))),
  "natlist_version_bcounter" -> nat_max(natlist_gcounter(natlist_pncounter(natlist_version_bcounter("Unit", properties)))),
  "bvlist_version_bcounter" -> bv_eq(bv_max(bvlist_gcounter(bvlist_pncounter(bvlist_version_bcounter("Unit", properties))))),
  "natlist_bcounter" -> nat_max(natlist_gcounter(natlist_pncounter(natlist_version_bcounter(natlist_bcounter("Unit", properties))))),
  "bvlist_bcounter" -> bv_eq(bv_max(bvlist_gcounter(bvlist_pncounter(bvlist_version_bcounter(bvlist_bcounter("Unit", properties)))))),
  "natmap_gcounter" -> nat_max(natmap_gcounter("Unit", properties)),
  "bvmap_gcounter" -> bv_eq(bv_max(bvmap_gcounter("Unit", properties))),
  "natmap_pncounter" -> nat_max(natmap_pncounter("Unit", properties)),
  "bvmap_pncounter" -> bv_eq(bv_max(bvmap_pncounter("Unit", properties))),
  "natmap_bcounter" -> nat_max(natmap_bcounter("Unit", properties)),
  "bvmap_bcounter" -> bv_eq(bv_max(bvmap_bcounter("Unit", properties))),
  "nat_lwwreg" -> nat_max(nat_lwwreg("Unit", properties)),
  "nat_lwwreg_acc" -> nat_add2p(nat_max(nat_lwwreg_acc("Unit", properties))),
  "bv_lwwreg" -> bv_eq(bv_max(bv_lwwreg("Unit", properties))),
  "gset" -> gset("Unit", properties),
  "orset" -> nat_max(natlist_gcounter(orset("Unit", properties))),
  "twophaseset" -> twophaseset("Unit", properties))

def prop(property: Seq[String]) = property map {
  case "comm" => comm
  case "assoc" => assoc
  case "idem" => idem
  case "sel" => sel
  case "refl" => refl
  case "irefl" => irefl
  case "sym" => sym
  case "antisym" => antisym
  case "asym" => asym
  case "conn" => conn
  case "trans" => trans
  case _ => throw new IllegalArgumentException(s"Invalid property: $property")
}

@main def benchmark(benchmark: String, property: String*) =
  val errors = properties.check(benchmarks(prop(property))(benchmark), printDeductionDebugInfo = false, printReductionDebugInfo = false).showErrors
  if errors.nonEmpty then
    println(errors)
