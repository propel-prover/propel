package propel
package ast

case class Error(message: String) extends Enrichment(Error)

object Error extends Enrichment.Extrinsic[Type | Pattern | Term, Error]

extension (construct: Type | Pattern | Term)
  def errors: List[(Type | Pattern | Term, Error)] =
    val errors = (construct.info(Error) map { construct -> _ }).toList
    construct match
      case Match(_, args) => (args flatMap { _.errors }) ++ errors
      case Bind(_) => errors
      case Function(arg, result) => arg.errors ++ result.errors ++ errors
      case Universal(_, result) => result.errors ++ errors
      case Recursive(_, result) => result.errors ++ errors
      case TypeVar(_) => errors
      case Sum(sum) => (sum flatMap { (_, args) => args flatMap { _.errors } }) ++ errors
      case Abs(_, _, tpe, expr) => tpe.errors ++ expr.errors ++ errors
      case App(_, expr, arg) => expr.errors ++ arg.errors ++ errors
      case TypeAbs(_, expr) => expr.errors ++ errors
      case TypeApp(expr, tpe) => expr.errors ++ tpe.errors ++ errors
      case Data(_, args) => (args flatMap { _.errors }) ++ errors
      case Var(_) => errors
      case Cases(scrutinee, cases) => scrutinee.errors ++ (cases flatMap { _.errors ++ _.errors }) ++ errors

  def withoutErrors: Type | Pattern | Term = construct match
    case construct: Type => construct.withoutErrors
    case construct: Pattern => construct.withoutErrors
    case construct: Term => construct.withoutErrors

extension (pattern: Pattern)
  def withoutErrors: Pattern = pattern.withoutInfo(Error) match
    case pattern @ Match(ctor, args) => Match(pattern)(ctor, args map { _.withoutErrors })
    case pattern @ Bind(_) => pattern

extension (tpe: Type)
  def withoutErrors: Type = tpe.withoutInfo(Error) match
      case Function(arg, result) => Function(tpe)(arg.withoutErrors, result.withoutErrors)
      case Universal(ident, result) => Universal(tpe)(ident, result.withoutErrors)
      case Recursive(ident, result) => Recursive(tpe)(ident, result.withoutErrors)
      case TypeVar(_) => tpe
      case Sum(sum) => Sum(tpe)(sum map { (ctor, args) => ctor -> (args map { _.withoutErrors }) })

extension (expr: Term)
  def withoutErrors: Term = expr.withoutInfo(Error) match
    case term @ Abs(properties, ident, tpe, expr) => Abs(term)(properties, ident, tpe.withoutErrors, expr.withoutErrors)
    case term @ App(properties, expr, arg) => App(term)(properties, expr.withoutErrors, arg.withoutErrors)
    case term @ TypeAbs(ident, expr) => TypeAbs(term)(ident, expr.withoutErrors)
    case term @ TypeApp(expr, tpe) => TypeApp(term)(expr.withoutErrors, tpe.withoutErrors)
    case term @ Data(ctor, args) => Data(term)(ctor, args map { _.withoutErrors })
    case term @ Var(_) => term
    case term @ Cases(scrutinee, cases) => Cases(term)(scrutinee.withoutErrors, cases map { (pattern, expr) =>
      pattern.withoutErrors -> expr.withoutErrors
    })
