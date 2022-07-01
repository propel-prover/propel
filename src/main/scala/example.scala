package example

import dsl.*
import checker.*

def min(expr: Expr) =
  let(commutative)(
    "min",
    abs(commutative)(
      List(pattern("Z"), pattern("Z")) -> ctor("Z"),
      List(pattern("S", bind("a")), pattern("Z")) -> ctor("Z"),
      List(pattern("Z"), pattern("S", bind("b"))) -> ctor("Z"),
      List(pattern("S", bind("a")), pattern("S", bind("b"))) -> ctor("S", app(id("min"), id("a"), id("b")))),
    expr)

def max(expr: Expr) =
  let(commutative)(
    "max",
    abs(commutative)(
      List(pattern("Z"), pattern("Z")) -> ctor("Z"),
      List(pattern("S", bind("a")), pattern("Z")) -> ctor("S", id("a")),
      List(pattern("Z"), pattern("S", bind("b"))) -> ctor("S", id("b")),
      List(pattern("S", bind("a")), pattern("S", bind("b"))) -> ctor("S", app(id("max"), id("a"), id("b")))),
    expr)

def map(expr: Expr) =
  let(commutative)(
    "f",
    ctor("Z"),
    let(commutative)(
      "map",
      abs(commutative)(
        List(pattern("nil"), pattern("nil")) -> ctor("nil"),
        List(pattern("nil"), pattern("cons", bind("y"), bind("ys"))) -> ctor("nil"),
        List(pattern("cons", bind("x"), bind("xs")), pattern("nil")) -> ctor("nil"),
        List(pattern("cons", bind("x"), bind("xs")), pattern("cons", bind("y"), bind("ys"))) ->
          ctor("cons", app(id("f"), id("x"), id("y")), app(id("map"), id("xs"), id("ys")))),
      expr))

def othermap(expr: Expr) =
  let(commutative)(
    "f",
    ctor("Z"),
    let()(
      "g",
      ctor("Z"),
      let(commutative)(
        "othermap",
        abs(commutative)(
          List(pattern("nil"), pattern("nil")) -> ctor("nil"),
          List(pattern("nil"), pattern("cons", bind("y"), bind("ys"))) -> ctor("cons", app(id("g"), id("y")), app(id("othermap"), ctor("nil"), id("ys"))),
          List(pattern("cons", bind("x"), bind("xs")), pattern("nil")) -> ctor("cons", app(id("g"), id("x")), app(id("othermap"), id("xs"), ctor("nil"))),
          List(pattern("cons", bind("x"), bind("xs")), pattern("cons", bind("y"), bind("ys"))) ->
            ctor("cons", app(id("f"), id("x"), id("y")), app(id("othermap"), id("xs"), id("ys")))),
        expr)))


@main def example =
  val program = othermap(ctor("Z"))

  println()
  println("ORIGINAL:")
  println(program.show)

  println()
  println("ORIGINAL NORMALIZED:")
  println(normalize(program).show)

  println()
  println("SWAPPED:")
  println(swap(program).show)

  println()
  println("SWAPPED NORMALIZED:")
  println(normalize(swap(program)).show)

  check(program)
