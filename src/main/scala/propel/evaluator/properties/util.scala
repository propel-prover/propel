package propel
package evaluator
package properties

import ast.*
import typer.*
import util.*

def recursiveCalls(expr: Term): List[Term] =
  def recursiveCalls(term: Term, abstraction: Abstraction): List[Term] = term match
    case Abs(properties, ident, tpe, expr) =>
      recursiveCalls(expr, abstraction)
    case App(properties1, expr1 @ App(properties0, expr0, arg0), arg1) if expr0.info(Abstraction) contains abstraction =>
      expr0 :: recursiveCalls(expr1, abstraction) ++ recursiveCalls(arg1, abstraction)
    case App(properties, expr, arg) =>
      recursiveCalls(expr, abstraction) ++ recursiveCalls(arg, abstraction)
    case TypeAbs(ident, expr) =>
      recursiveCalls(expr, abstraction)
    case TypeApp(expr, tpe) =>
      recursiveCalls(expr, abstraction)
    case Data(ctor, args) =>
      args flatMap { recursiveCalls(_, abstraction) }
    case Var(ident) =>
      List.empty
    case Cases(scrutinee, cases) =>
      recursiveCalls(scrutinee, abstraction) ++ (cases flatMap { (_, expr) => recursiveCalls(expr, abstraction) })

  expr.info(Abstraction).toList flatMap { recursiveCalls(expr, _) }
end recursiveCalls

def patternsByType(tpe: Type, base: String, names: Set[String]): List[Pattern] =
  val syntactic = tpe.syntacticInfo
  val stop = Symbol(Naming.freshIdent("⏹", syntactic.freeTypeVars ++ syntactic.boundTypeVars map { _.name }))

  def recursionStop(tpe: Type) = Universal(stop, tpe)

  def recursionBase(tpe: Type, names: Set[String]) =
    val patternType = tpe match
      case Universal(`stop`, tpe) => tpe
      case _ => tpe

    val name = Naming.freshIdent(base, names)
    Bind(Symbol(name)).withExtrinsicInfo(Typing.Specified(Right(patternType))) -> (names + name)

  def patternsByType(tpe: Type, names: Set[String]): List[(Pattern, Set[String])] = tpe match
    case Sum(sum) =>
      sum flatMap { (ctor, args) =>
        val argsPatterns = args.foldLeft(List(List.empty[Pattern] -> names)) { (argsPatterns, arg) =>
          argsPatterns flatMap { (argPatterns, names) =>
            patternsByType(arg, names) map { (argPattern, names) => (argPattern :: argPatterns) -> names }
          }
        }
        argsPatterns map { (args, names) => Match(ctor, args.reverse) -> names }
      }
    case Recursive(ident, result) =>
      recursionBase(tpe, names) :: patternsByType(subst(result, Map(ident -> recursionStop(tpe))), names)
    case _ =>
      List(recursionBase(tpe, names))

  patternsByType(tpe, names) map { (patterns, _) => patterns }
end patternsByType
