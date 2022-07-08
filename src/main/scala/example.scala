package example

import dsl.*
import dsl.sugar.*
import checker.*


def min[A: TermExpr](expr: A) =
  let(
    "min",
    abs(comm)("a", "b")(cases("Pair", "a", "b")(
      ("Pair", ("S", "a"), ("S", "b")) -> ("S", app(comm)("min", "a", "b")),
      ("_") -> "Z")),
    expr)

def max[A: TermExpr](expr: A) =
  let(
    "max",
    abs(comm)("a", "b")(cases("Pair", "a", "b")(
      ("Pair", ("S", "a"), ("S", "b")) -> ("S", app(comm)("max", "a", "b")),
      ("Pair", "a", "Z") -> "a",
      ("Pair", "Z", "a") -> "a")),
    expr)

def ordernat[A: TermExpr](expr: A) =
  let(
    "ordernat",
    abs(antisym, trans)("a", "b")(let("pair", ("Pair", "a", "b"),
      cases("pair")(
        ("Pair", ("S", "x"), ("S", "y")) -> app(antisym, trans)("ordernat", "x", "y"),
        ("Pair", "Z", "_") -> True,
        ("_") -> False))),
    expr)

def orderlist[A: TermExpr](expr: A) =
  let(
    "orderlist",
    abs(antisym, trans)("a", "b")(let("pair", ("Pair", "a", "b"),
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
          False))),
    expr)

def map[A: TermExpr](expr: A) =
  let(
    "map",
    abs(comm)("a", "b")(cases("Pair", "a", "b")(
      ("Pair", ("Cons", "x", "xs"), ("Cons", "y", "ys")) -> ("Cons", app(comm)("f", "x", "y"), app(comm)("map", "xs", "ys")),
      ("_") -> "Nil")),
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
  val ast.Let(Symbol(name), fun: ast.Abs, _) = program
  println(program.show)

  {
    println()
    println(s"ANTISYMM CHECK for $name:")
    val prepared @ ast.Abs(_, _, _) = alpharename(antisymmetry.prepare(fun))
    println(prepared.show)

    val result = eval(name, prepared)

    println()
    println(s"ANTISYMM CHECK for $name:")
    println(if antisymmetry.check(name, prepared, result) then "✔ true" else "✘ false")
  }

  {
    println()
    println(s"TRANS CHECK for $name:")
    val prepared @ ast.Abs(_, _, _) = alpharename(transitivity.prepare(fun))
    println(prepared.show)

    val result = eval(name, prepared)

    println()
    println(s"TRANS CHECK for $name:")
    println(if transitivity.check(name, prepared, result) then "✔ true" else "✘ false")
  }


def exampleCommutative(program: Term) =
  println()
  println("PROGRAM:")
  val ast.Let(Symbol(name), fun: ast.Abs, _) = program
  println(program.show)

  {
    println()
    println(s"COMM CHECK for $name:")
    val prepared @ ast.Abs(_, _, _) = alpharename(commutativity.prepare(fun))
    println(prepared.show)

    val result = eval(name, prepared)

    println()
    println(s"COMM CHECK for $name:")
    println(if commutativity.check(name, prepared, result) then "✔ true" else "✘ false")
  }


def eval(name: String, prepared: ast.Abs) =
  println()
  println(s"SYMBOL EVAL for $name:")

  val result = Symbolic.eval(prepared)

  println((result.reductions map { case Symbolic.Reduction(expr, Symbolic.Constraints(pos, neg)) =>
    "• " + expr.show + "\n" +
    (pos map { (expr, pattern) => expr.show + "≔" + pattern.show }).mkString("  pos: {", ", ", "}\n") +
    (neg map { neg => (neg map { (expr, pattern) => expr.show + "≔" + pattern.show }).mkString("{", ", ", "}") }).mkString("  neg: {", ", ", "}")
  }).mkString("\n\n"))

  result
