package propel

import ast.*
import dsl.*
import dsl.sugar.*
import evaluator.*


def merge[A: TermExpr](expr: A) =
  letrec(
    "merge" -> abs(comm)("a", "b")(
      cases("Pair", "a", "b")(
        ("Pair", "Nil", "Nil") -> "Nil",
        ("Pair", ("Cons", "a", "as"), "Nil") -> ("Cons", "a", "as"),
        ("Pair", "Nil", ("Cons", "b", "bs")) -> ("Cons", "b", "bs"),
        ("Pair", ("Cons", "a", "as"), ("Cons", "b", "bs")) ->
             `if`("=", "a", "b")
                 ("Cons", "a", ("Cons", "b", ("merge", "as", "bs")))
                 (`if`("<", "a", "b")                       
                      ("Cons", "a", ("merge", "as", ("Cons", "b", "bs")))
                      ("Cons", "b", ("merge", ("Cons", "a", "as"), "bs"))))))(
    expr)

def min[A: TermExpr](expr: A) =
  letrec(
    "min" -> abs(comm)("a", "b")(cases("Pair", "a", "b")(
      ("Pair", ("S", "a"), ("S", "b")) -> ("S", app(comm)("min", "a", "b")),
      ("_") -> "Z")))(
    expr)

def max[A: TermExpr](expr: A) =
  letrec(
    "max" -> abs(comm)("a", "b")(cases("Pair", "a", "b")(
      ("Pair", ("S", "a"), ("S", "b")) -> ("S", app(comm)("max", "a", "b")),
      ("Pair", "a", "Z") -> "a",
      ("Pair", "Z", "a") -> "a")))(
    expr)

def ordernat[A: TermExpr](expr: A) =
  letrec(
    "ordernat" -> abs(antisym, trans)("a", "b")(let("pair" -> ("Pair", "a", "b"))(
      cases("pair")(
        ("Pair", ("S", "x"), ("S", "y")) -> app(antisym, trans)("ordernat", "x", "y"),
        ("Pair", "Z", "_") -> True,
        ("_") -> False))))(
    expr)

def orderlist[A: TermExpr](expr: A) =
  letrec(
    "orderlist" -> abs(antisym, trans)("a", "b")(let("pair" -> ("Pair", "a", "b"))(
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
    "map" -> abs(comm)("a", "b")(cases("Pair", "a", "b")(
      ("Pair", ("Cons", "x", "xs"), ("Cons", "y", "ys")) -> ("Cons", app(comm)("f", "x", "y"), app(comm)("map", "xs", "ys")),
      ("_") -> "Nil")))(
    expr)


@main def example =
  exampleAntisymmAndTransitive(ordernat("Z"))
  exampleAntisymmAndTransitive(orderlist("Z"))
  exampleCommutative(min("Z"))
  exampleCommutative(max("Z"))
  exampleCommutative(map("Z"))


def exampleAntisymmAndTransitive(program: Term) =
  println()
  println("PROGRAM:")

  val App(_,
    Abs(_, _, Cases(_, List(Match(_, List(Bind(Symbol(name)))) -> _))),
    App(_, _, Abs(_ , _, Abs(_, _, Data(_, List(fun: Abs)))))) = program

  println(program.show)

  {
    println()
    println(s"ANTISYMM CHECK for $name:")
    val prepared @ Abs(_, _, body: Abs) =
      AlphaConversion.uniqueNames(properties.antisymmetry.prepare(fun)).expr
    println(body.show)

    val result = eval(name, body)

    println()
    println(s"ANTISYMM CHECK for $name:")
    println(if properties.antisymmetry.check(name, prepared, result) then "✔ true" else "✘ false")
  }

  {
    println()
    println(s"TRANS CHECK for $name:")
    val prepared @ Abs(_, _, Abs(_, _, body: Abs)) =
      AlphaConversion.uniqueNames(properties.transitivity.prepare(fun)).expr
    println(body.show)

    val result = eval(name, body)

    println()
    println(s"TRANS CHECK for $name:")
    println(if properties.transitivity.check(name, prepared, result) then "✔ true" else "✘ false")
  }


def exampleCommutative(program: Term) =
  println()
  println("PROGRAM:")

  val App(_,
    Abs(_, _, Cases(_, List(Match(_, List(Bind(Symbol(name)))) -> _))),
    App(_, _, Abs(_ , _, Abs(_, _, Data(_, List(fun: Abs)))))) = program

  println(program.show)

  {
    println()
    println(s"COMM CHECK for $name:")
    val prepared @ Abs(_, _, body: Abs) =
      AlphaConversion.uniqueNames(properties.commutativity.prepare(fun)).expr
    println(body.show)

    val result = eval(name, body)

    println()
    println(s"COMM CHECK for $name:")
    println(if properties.commutativity.check(name, prepared, result) then "✔ true" else "✘ false")
  }


def eval(name: String, body: Abs) =
  def parenthesize(value: Term | Pattern) = value match
    case value @ (Bind(_) | Match(_, List())) => value.show
    case value @ (Var(_) | Data(_, List())) => value.show
    case value: Term => s"(${value.show})"
    case value: Pattern => s"(${value.show})"

  println()
  println(s"SYMBOL EVAL for $name:")

  val result = Symbolic.eval(body)

  println((result.reductions map { case Symbolic.Reduction(expr, Symbolic.Constraints(pos, neg)) =>
    "• " + expr.show + "\n" +
    (pos map { (expr, pattern) =>
      parenthesize(expr) + "≔" + parenthesize(pattern)
    }).mkString("  pos: {", ", ", "}\n") +
    (neg map { neg =>
      (neg map { (expr, pattern) => parenthesize(expr) + "≔" + parenthesize(pattern) }).mkString("{", ", ", "}")
    }).mkString("  neg: {", ", ", "}")
  }).mkString("\n\n"))

  result
