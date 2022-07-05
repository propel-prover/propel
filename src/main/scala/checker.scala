package checker

import ast.*
import dsl.show
import ordering.given
import scala.collection.mutable


def fail(message: String) = throw RuntimeException(message)


def subscript(i: Int) =
  def subscript(i: Int) = i.toString map { c => (c.toInt - '0' + '₀').toChar }
  if i < 0 then "₋" + subscript(-i) else subscript(i)


def alpharename(expr: Term): Term =
  val used = mutable.Set.empty[String]

  def freshName(base: String, index: Int): String =
    val name = base + subscript(index)
    if used.contains(name) then freshName(base, index + 1) else name

  def renameCase(pattern: Case): (Case, Map[String, String]) = pattern match
    case Pattern(ident, args) =>
      val (renamedArgs, substs) = args.map(renameCase).unzip
      (Pattern(ident, renamedArgs), substs.foldLeft(Map.empty) { _ ++ _ })
    case Bind(ident) =>
      val fresh = freshName(ident.name, 1)
      used += fresh
      (Bind(Symbol(fresh)), Map(ident.name -> fresh))

  def renameTerm(expr: Term, subst: Map[String, String], applicator: Boolean = false): Term = expr match
    case Abs(properties, args, expr) =>
      val (renamedArgs, additionalSubst) = (args map { arg =>
        val fresh = freshName(arg.name, 1)
        used += fresh
        (Symbol(fresh), arg.name -> fresh)
      }).unzip
      Abs(properties, renamedArgs, renameTerm(expr, subst ++ additionalSubst))
    case App(properties, expr, args) =>
      App(properties, renameTerm(expr, subst, applicator = true), args map { renameTerm(_, subst) })
    case Ident(ident) =>
      subst.get(ident.name) match
        case Some(name) => Ident(Symbol(name))
        case _ if applicator => expr 
        case _ => fail(s"Unbound identifier: ${ident.name}")
    case Let(ident, bound, expr) =>
      val fresh = freshName(ident.name, 1)
      used += fresh
      Let(Symbol(fresh), renameTerm(bound, subst + (ident.name -> fresh)), renameTerm(expr, subst + (ident.name -> fresh)))
    case Cases(scrutinee, cases) =>
      val renamedScrutinee = renameTerm(scrutinee, subst)
      val renamedCases = cases map { (pattern, expr) =>
        val (renamedPattern, additionalSubst) = renameCase(pattern)
        renamedPattern -> renameTerm(expr, subst ++ additionalSubst)
      }
      Cases(renamedScrutinee, renamedCases)

  renameTerm(expr, Map.empty)


enum Unification:
  case Full(substs: Map[Symbol, Term])
  case Irrefutable(substs: Map[Symbol, Term], residuals: Set[Case])
  case Distinct

def unify(pattern: Case, expr: Term): Unification =
  def unify(pattern: Case, expr: Term): Option[(Map[Symbol, Term], Set[Case])] = pattern -> expr match
    case Pattern(patternIdent, patternArgs) -> App(_, Ident(exprIdent), exprArgs)
        if patternIdent == exprIdent && patternArgs.size == exprArgs.size =>
      if patternArgs.nonEmpty then
        patternArgs zip exprArgs map unify reduce {
          case (Some(substs0, residuals0), Some(substs1, residuals1)) =>
            Some(substs0 ++ substs1, residuals0 ++ residuals1)
          case _ =>
            None
        }
      else
        Some(Map.empty, Set.empty)
    case Bind(ident) -> expr =>
      Some(Map(ident -> expr), Set.empty)
    case pattern -> Ident(_) =>
      Some(Map.empty, Set(pattern))
    case _ =>
      None

  unify(pattern, expr) match
    case Some(substs, residuals) if residuals.isEmpty => Unification.Full(substs)
    case Some(substs, residuals) => Unification.Irrefutable(substs, residuals)
    case _ => Unification.Distinct


def replaceBinds(pattern: Case, subst: Case): Case = pattern match
  case Pattern(ident, args) =>
    Pattern(ident, args map { replaceBinds(_, subst) })
  case Bind(_) =>
    subst


def enmuerateBinds(imputs: List[List[Case]]): List[List[Case]] =
  var index = 0

  def enmuerateBinds(pattern: Case): Case = pattern match
    case Pattern(ident, args) =>
      Pattern(ident, args map enmuerateBinds)
    case Bind(_) =>
      index += 1
      Bind(Symbol("□" + subscript(index)))

  imputs.map { cases =>
    index = 0
    cases map enmuerateBinds
  }


def inputspace(fun: Abs): Set[Case] =
  val result = mutable.Set.empty[Case]

  def inputspace(expr: Term, space: Set[Case]): Unit = expr match
    case Abs(_, args, expr) =>
      inputspace(expr, space)
    case App(_, expr, args) =>
      inputspace(expr, space)
      args foreach { inputspace(_, space) }
    case Ident(_) =>
      result ++= space
    case Let(_, bound, expr) =>
      inputspace(bound, space)
      inputspace(expr, space)
    case Cases(scrutinee, cases) =>
      inputspace(scrutinee, space)
      cases foreach { (pattern, expr) =>
        unify(pattern, scrutinee) match {
          case Unification.Irrefutable(_, residuals) =>
            val generalized = residuals map { replaceBinds(_, Bind(Symbol("□"))) }
            val additonals = space flatMap { pattern => generalized map { replaceBinds(pattern, _) } }
            inputspace(expr, space ++ additonals)
          case _ =>
        }
      }

  inputspace(fun, Set(Bind(Symbol("□"))))
  result.toSet


def inputs(inputspace: Set[Case], dimension: Int): List[List[Case]] =
  def combinations(patterns: List[Case], rest: Int): List[List[Case]] =
    if rest > 0 then
      val tail = combinations(patterns, rest - 1)
      patterns flatMap { pattern => tail map { pattern :: _ } }
    else
      List.fill(dimension)(List.empty)

  combinations(inputspace.toList, dimension).distinct


def inputarg(input: Case): Term = input match
  case Pattern(ident, args) => App(Set.empty, Ident(ident), args map inputarg)
  case Bind(ident) => Ident(ident)


def subst(expr: Term, substs: Map[Symbol, Term]): Term =
  def bound(pattern: Case): List[Symbol] = pattern match
    case Pattern(ident, args) => args flatMap bound
    case Bind(ident) => List(ident)

  def subst(expr: Term, substs: Map[Symbol, Term]): Term = expr match
    case Abs(properties, args, expr) =>
      Abs(properties, args, subst(expr, substs -- args))
    case App(properties, expr, args) =>
      App(properties, subst(expr, substs), args map { subst(_, substs) })
    case Ident(ident) =>
      substs.getOrElse(ident, expr)
    case Let(ident, bound, expr) =>
      Let(ident, subst(bound, substs), subst(expr, substs - ident))
    case Cases(scrutinee, cases) =>
      Cases(
        subst(scrutinee, substs),
        cases map { (pattern, expr) =>
          pattern -> subst(expr, substs -- bound(pattern))
        })

  subst(expr, substs)


def partialeval(fun: Abs, args: List[Term]): Term =
  def contains(expr: Term, ident: Symbol): Boolean = expr match
    case Abs(_, args, expr) => contains(expr, ident)
    case App(_, expr, args) => contains(expr, ident) || (args exists { contains(_, ident) })
    case Ident(`ident`) => true
    case Ident(_) => false
    case Let(_, bound, expr) => contains(bound, ident) || contains(expr, ident)
    case Cases(scrutinee, cases) => contains(scrutinee, ident) || (cases exists { (_, expr) => contains(expr, ident) })

  def partialeval(expr: Term): Term = expr match
    case Abs(properties, args, expr) =>
      Abs(properties, args, partialeval(expr))
    case App(properties, expr, args) =>
      App(properties, partialeval(expr), args map partialeval)
    case Ident(ident) =>
      expr
    case Let(ident, bound, expr) =>
      if contains(bound, ident) then
        Let(ident, partialeval(bound), partialeval(expr))
      else
        partialeval(subst(expr, Map(ident -> bound)))
    case Cases(scrutinee, cases) =>
      val evaluatedScrutinee = partialeval(scrutinee)

      def process(cases: List[(Case, Term)]): Option[(Case, Term)] = cases match
        case (pattern, expr) :: tail =>
          unify(pattern, evaluatedScrutinee) match 
            case Unification.Full(substs) =>
              Some(pattern -> subst(expr, substs))
            case _ =>
              process(tail)
        case _ =>
          None

      process(cases) match
        case Some(_ -> expr) => partialeval(expr)
        case None => Ident(Symbol("∅"))

  if fun.args.size != args.size then
    fail(s"Wrong number of arguments: ${args.size} (expected: ${fun.args.size})")

  partialeval(subst(fun.expr, (fun.args zip args).toMap))


object commutativity:
  def inputs(inputspace: Set[Case]): List[List[Case]] =
    enmuerateBinds(checker.inputs(inputspace, 2).map(_.sorted).distinct) filter {
      case List(a, b) => a != b
      case _ => true 
    }

  def normalize(expr: Term): Term = expr match
    case Abs(properties, args, expr) =>
      Abs(properties, args, normalize(expr))
    case App(properties, expr, List(arg0, arg1)) if properties.contains(Property.Commutative) =>
      val normalizedArg0 = normalize(arg0)
      val normalizedArg1 = normalize(arg1)
      if normalizedArg0 < normalizedArg1 then
        App(properties, normalize(expr), List(normalizedArg0, normalizedArg1))
      else
        App(properties, normalize(expr), List(normalizedArg1, normalizedArg0))
    case App(properties, expr, args) =>
      App(properties, normalize(expr), args map normalize)
    case Ident(ident) =>
      expr
    case Let(ident, bound, expr) =>
      Let(ident, normalize(bound), normalize(expr))
    case Cases(scrutinee, cases) =>
      Cases(normalize(scrutinee), cases map { (pattern, expr) => pattern -> normalize(expr) })

  def normalize(fun: Abs, inputs: List[Case]): Term =
    normalize(partialeval(fun, inputs map inputarg))

  def check(fun: Abs): Boolean =
    inputs(inputspace(fun)) forall { inputs =>
      val args = inputs map inputarg
      normalize(partialeval(fun, args)) equiv normalize(partialeval(fun, args.reverse))
    }
