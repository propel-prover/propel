package propel
package evaluator
package properties

import ast.*
import typer.*
import util.*

def recursiveCall(expr: Term): Option[Term] =
  val free = expr.syntacticInfo.freeVars.keySet

  def recursiveCall(term: Term, abstraction: Abstraction): Option[Term] = term match
    case Abs(properties, ident, tpe, expr) =>
      recursiveCall(expr, abstraction)
    case App(properties1, expr1 @ App(properties0, expr0, arg0), arg1) if expr0.info(Abstraction) contains abstraction =>
      if (term.syntacticInfo.freeVars.keySet --
          arg0.syntacticInfo.freeVars.keys --
          arg1.syntacticInfo.freeVars.keys) subsetOf free then
        Some(expr0)
      else
        recursiveCall(expr1, abstraction) orElse recursiveCall(arg1, abstraction)
    case App(properties, expr, arg) =>
      recursiveCall(expr, abstraction) orElse recursiveCall(arg, abstraction)
    case TypeAbs(ident, expr) =>
      recursiveCall(expr, abstraction)
    case TypeApp(expr, tpe) =>
      recursiveCall(expr, abstraction)
    case Data(ctor, args) =>
      args collectFirstDefined { recursiveCall(_, abstraction) }
    case Var(ident) =>
      None
    case Cases(scrutinee, cases) =>
      recursiveCall(scrutinee, abstraction) orElse {
        cases collectFirstDefined { (_, expr) => recursiveCall(expr, abstraction) }
      }

  expr.info(Abstraction) flatMap { recursiveCall(expr, _) }
end recursiveCall

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
