package example

import dsl.*
import checker.*

def min(expr: Term) =
  let(
    "min",
    abs(comm)("a", "b")(cases("Pair", "a", "b")(
      ("Pair", "a", "Z") -> "Z",
      ("Pair", "Z", "a") -> "Z",
      ("Pair", ("S", "a"), ("S", "b")) -> ("S", app(comm)("min", "a", "b")))),
    expr)

def max(expr: Term) =
  let(
    "max",
    abs(comm)("a", "b")(cases("Pair", "a", "b")(
      ("Pair", "a", "Z") -> "a",
      ("Pair", "Z", "a") -> "a",
      ("Pair", ("S", "a"), ("S", "b")) -> ("S", app(comm)("max", "a", "b")))),
    expr)

def map(expr: Term) =
  let(
    "map",
    abs(comm)("a", "b")(cases("Pair", "a", "b")(
      ("Pair", ("Cons", "x", "xs"), ("Cons", "y", "ys")) -> ("Cons", app(comm)("f", "x", "y"), app(comm)("map", "xs", "ys")),
      ("_") -> "Nil")),
    expr)


@main def example =
  val program = alpharename(map(term("Z")))

  println()
  println("PROGRAM:")
  println(program.show)

  val ast.Let(Symbol(name), fun: ast.Abs, _) = program

  println()
  println(s"INPUTSPACE for $name:")
  val space = inputspace(fun)
  println(space.map(_.show).mkString(", "))

  println()
  println(s"INPUTS for COMMUTATIVITY CHECK for $name:")
  val inputs = commutativity.inputs(space)
  println(inputs.map(_.map(_.show).mkString("❬", ", ", "❭")).mkString(", "))

  inputs map { inputs =>
    println()
    println(s"COMMUTATIVITY NORMAL with ${inputs.map(_.show).mkString("❬", ", ", "❭")} for $name:")
    println(commutativity.normalize(fun, inputs).show)

    println()
    println(s"COMMUTATIVITY NORMAL with ${inputs.reverse.map(_.show).mkString("❬", ", ", "❭")} (reversed) for $name:")
    println(commutativity.normalize(fun, inputs.reverse).show)
  }

  println()
  println(s"COMMUTATIVITY CHECK for $name:")
  println(commutativity.check(fun))
