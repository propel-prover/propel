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
    "min" -> tp(nat -> (nat -> nat)) -> abs(comm)("a" -> nat, "b" -> nat)(cases("Pair", "a", "b")(
      ("Pair", ("S", "a"), ("S", "b")) -> ("S", app(comm)("min", "a", "b")),
      ("_") -> "Z")))(
    expr)

def max[A: TermExpr](expr: A) =
  letrec(
    "max" -> tp(nat -> (nat -> nat)) -> abs(comm)("a" -> nat, "b" -> nat)(cases("Pair", "a", "b")(
      ("Pair", ("S", "a"), ("S", "b")) -> ("S", app(comm)("max", "a", "b")),
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


@main def example =
  def check(expr: Term) =
    val result = properties.check(expr, printDebugInfo = true)
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
