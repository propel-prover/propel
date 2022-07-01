package dsl

import ast.*

type Expr = Term

def commutative =
  Property.Commutative

def pattern(name: String, args: Case*) =
  Case.Pattern(Ident.Type(name), args.toList)

def bind(name: String) =
  Case.Bind(Ident.Term(name))

def abs(case0: (List[Case], Term), caseN: (List[Case], Term)*) =
  Term.Abs(Set.empty, case0 :: caseN.toList)

def abs(properties: Property*)(case0: (List[Case], Term), caseN: (List[Case], Term)*) =
  Term.Abs(properties.toSet, case0 :: caseN.toList)

def app(expr: Term, args: Term*) =
  Term.App(expr, args.toList)

def id(name: String) =
  Term.Var(Ident.Term(name))

def ctor(name: String, args: Term*) =
  Term.Ctor(Ident.Type(name), args.toList)

def let(name: String, bound: Term, expr: Term) =
  Term.Let(Set.empty, Ident.Term(name), bound, expr)

def let(properties: Property*)(name: String, bound: Term, expr: Term) =
  Term.Let(properties.toSet, Ident.Term(name), bound, expr)


extension (properties: Properties) def show: String =
  properties.map(_.toString.toLowerCase).mkString(", ")

extension (expr: Case) def show: String = expr match
  case Case.Pattern(Ident.Type(name), List()) => name
  case Case.Pattern(Ident.Type(name), args) => s"($name ${args.map(_.show).mkString(" ")})"
  case Case.Bind(Ident.Term(name)) => name

extension (cases: List[Case]) def show: String =
  s"❬${cases.map(_.show).mkString(", ")}❭"

extension (expr: Term) def show: String =
  def show(expr: Term, indent: Int): String =
    def showDirect(expr: Term) = show(expr, indent)
    def showInline(expr: Term) = show(expr, indent + 1)
    def showAlinged(output: String) = s"\n${"  " * indent}$output"
    def showIndented(expr: Term) = s"\n${"  " * (indent + 1)}${show(expr, indent + 1)}"

    expr match
      case Term.Abs(properties, cases) =>
        val annotation = if properties.isEmpty then "" else s"[${properties.show}] "
        s"${annotation}λcase${cases.map((cases, expr) => showAlinged(s"${cases.show} ⇒ ${showInline(expr)}")).mkString}"
      case Term.App(expr, List()) =>
        showDirect(expr)
      case Term.App(expr, args) =>
        s"(${showDirect(expr)} ${args.map(showDirect).mkString(" ")})"
      case Term.Var(Ident.Term(name)) =>
        name
      case Term.Ctor(Ident.Type(name), List()) =>
        name
      case Term.Ctor(Ident.Type(name), args) =>
        s"($name ${args.map(showDirect).mkString(" ")})"
      case Term.Let(properties, Ident.Term(name), bound, expr) =>
        val annotation = if properties.isEmpty then "" else s"[${properties.show}] "
        s"let $annotation$name = ${showInline(bound)}${showAlinged("in")}${showIndented(expr)}"

  show(expr, 0)
