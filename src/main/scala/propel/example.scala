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
    "map" -> forall("T", "U", "R")(("T" -> ("U" -> "R")) -> (list("T") -> (list("U") -> list("R")))) ->
      tpabs("T", "U", "R")(abs(comm)("f" -> tp("T" -> ("U" -> "R")), "a" -> list("T"), "b" -> list("U"))(cases("Pair", "a", "b")(
        ("Pair", ("Cons", "x", "xs"), ("Cons", "y", "ys")) ->
          ("Cons", app(comm)("f", "x", "y"), app(comm)((tpapp("map")(tp("T"), tp("U"), tp("R")), "f"), "xs", "ys")),
        ("_") ->
          "Nil"))))(
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

  val (typedProgram @ Cases(
    App(_, App(_, _, Abs(_, _, _,Abs(_, _, _, Data(_, List(fun: Abs))))), _),
    List(Match(_, List(Bind(Symbol(name)))) -> _)), tpe) = program.typed

  println(program.show)

  if tpe.isEmpty then
    println()
    println(typedProgram.showErrors)

  println()
  println("TYPE:")
  println(fun.info(Typing.Term).flatMap(_.tpe.map(_.show)))

  {
    println()
    println(s"ANTISYMM CHECK for $name:")
    val prepared @ Abs(_, _, _, body: Abs) =
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
    val prepared @ Abs(_, _, _, Abs(_, _, _, body: Abs)) =
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

  val (typedProgram @ Cases(
    App(_, App(_, _, Abs(_, _, _,Abs(_, _, _, Data(_, List(definition))))), _),
    List(Match(_, List(Bind(Symbol(name)))) -> _)), tpe) = program.typed

  val fun = (definition: @unchecked) match
    case fun: Abs => fun
    case TypeAbs(_, TypeAbs(_, TypeAbs(_, Abs(_, _, _, fun: Abs)))) => fun

  println(program.show)

  if tpe.isEmpty then
    println()
    println(typedProgram.showErrors)

  println()
  println("TYPE:")
  println(definition.info(Typing.Term).flatMap(_.tpe.map(_.show)))

  {
    println()
    println(s"COMM CHECK for $name:")
    val prepared @ Abs(_, _, _, body: Abs) =
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
