package propel
package printing
package impl

import ast.*
import Constructor.*
import Format.*


enum Format:
  case Indentation
  case Open(content: String)
  case Close(content: String)(val opening: Format)
  case Plain(content: String)
  case Keyword(content: String)
  case Start(construct: Type | Pattern | Term)
  case End(construct: Type | Pattern | Term)

extension (format: Format)
  @annotation.targetName("formatAsString")
  def asString: String = format match
    case Indentation => "  "
    case Open(content) => content
    case Close(content) => content
    case Plain(content) => content
    case Keyword(content) => content
    case Start(_) => ""
    case End(_) => ""

extension (format: List[Format])
  @annotation.targetName("formatListAsString")
  def asString: String = (format map { _.asString }).mkString

extension (format: List[List[Format]])
  @annotation.targetName("formatListListAsString")
  def asString: String = (format map { _.asString }).mkString("\n")

  def range(construct: Type | Pattern | Term): Option[((Int, Int), (Int, Int))] =
    var start = Option.empty[(Int, Int)]
    var end = Option.empty[(Int, Int)]
    format.zipWithIndex foreach { (format, line) =>
      var column = 0
      format foreach {
        case format: Start if (format.construct eq construct) && start.isEmpty => start = Some(line, column)
        case format: End if format.construct eq construct => end = Some(line, column)
        case format => column += format.asString.length
      }
    }
    start flatMap { start => end map { (start, _) } }


extension (tpe: Type) def format: List[Format] =
  val format = tpe match
    case Function(
        arg @ (TypeVar(_) | Sum(List()) | Sum(List(_ -> List()))),
        result @ (TypeVar(_) | Sum(List()) | Sum(List(_ -> List())) | Function(_, _))) =>
      arg.format ++ (Plain(" ") :: Keyword("→") :: Plain(" ") :: result.format)
    case Function(arg @ (TypeVar(_) | Sum(List()) | Sum(List(_ -> List()))), result) =>
      val open = Open("(")
      arg.format ++ (Plain(" ") :: Keyword("→") :: Plain(" ") :: open :: (result.format :+ Close(")")(open)))
    case Function(arg, result @ (TypeVar(_) | Sum(List()) | Sum(List(_ -> List())) | Function(_, _))) =>
      val open = Open("(")
      (open :: arg.format) ++ (Close(")")(open) :: Plain(" ") :: Keyword("→") :: Plain(" ") :: result.format)
    case Function(arg, result) =>
      val open0 = Open("(")
      val open1 = Open("(")
      (open0 :: arg.format) ++ (Close(")")(open0) :: Plain(" ") :: Keyword("→") :: Plain(" ") :: open1 :: (result.format :+ Close(")")(open1)))
    case Universal(ident, result: Universal) =>
      Keyword("∀") :: Plain(" ") :: Plain(ident.name) :: result.format.patch(1, List.empty, 1)
    case Universal(ident, result) =>
      Keyword("∀") :: Plain(" ") :: Plain(ident.name) :: Keyword(".") :: Plain(" ") :: result.format
    case Recursive(ident, result) =>
      Keyword("µ") :: Plain(" ") :: Plain(ident.name) :: Keyword(".") :: Plain(" ") :: result.format
    case TypeVar(ident) =>
      List(Plain(ident.name))
    case Sum(List()) =>
      List(Plain("⊥"))
    case Sum(List(ctor -> List())) =>
      val open = Open("(")
      List(open, Plain(ctor.ident.name), Close(")")(open))
    case Sum(sum) =>
      val elements = sum map {
        case (ctor, List()) =>
          List(Plain(ctor.show))
        case (ctor, args) =>
          val elements = args map {
            case arg @ (TypeVar(_) | Sum(List()) | Sum(List(_ -> List()))) =>
              arg.format
            case arg =>
              val open = Open("(")
              open :: (arg.format :+ Close(")")(open))
          }
          Plain(ctor.show) :: (elements flatMap { Plain(" ") :: _ })
      }
      elements.head ++ (elements.tail flatMap { Plain(" ") :: Keyword("+") :: Plain(" ") :: _ })

  Start(tpe) :: (format :+ End(tpe))


extension (pattern: Pattern) def format: List[Format] =
  val format = pattern match
    case Match(ctor, List()) if ctor == True || ctor == False || (ctor.ident.name.headOption exists { _.isUpper }) =>
      List(Plain(ctor.ident.name))
    case Match(ctor, List()) =>
      val open = Open("(")
      List(open, Plain(ctor.ident.name), Close(")")(open))
    case Match(ctor, args) =>
      Plain(ctor.ident.name) :: (args flatMap {
        case arg @ Match(_, args) if args.nonEmpty =>
          val matcharg = arg.format
          matcharg.init.last match
            case close: Close if close.opening eq matcharg.tail.head =>
              Plain(" ") :: matcharg
            case _ =>
              val open = Open("(")
              Plain(" ") :: open :: (matcharg :+ Close(")")(open))
        case arg =>
          Plain(" ") :: arg.format
      })
    case Bind(ident) =>
      List(Plain(ident.name))

  Start(pattern) :: (format :+ End(pattern))


extension (expr: Term) def format: List[List[Format]] =
  val falseMatch = Match(False, List.empty)
  val falseData = Data(False, List.empty)
  val trueMatch = Match(True, List.empty)
  val trueData = Data(True, List.empty)

  def annotation(properties: Properties) =
    if properties.isEmpty then "" else s"[${properties.show}] "

  def indented(values: List[List[Format]]) =
    if values forall { _.head == Indentation } then values else values map { Indentation :: _ }

  def parenthesize(format: List[List[Format]]) =
    val head = (format.head.dropWhile {
      case Start(_) | End(_) | Keyword("¬") => true
      case _ => false
    }).headOption

    val last = (format.last.reverse.dropWhile {
      case Start(_) | End(_) => true
      case _ => false
    }).headOption

    (head, last) match
      case (Some(open), Some(close: Close)) if close.opening eq open =>
        format
      case _ if format.lengthCompare(1) > 0 =>
        val open = Open("(")
        (open :: format.head) :: (format.init.tail :+ (format.last :+ Close(")")(open)))
      case _ =>
        val open = Open("(")
        List(open :: (format.head :+ Close(")")(open)))

  def deparenthesize(format: List[List[Format]]) =
    val headIndex = format.head.indexWhere {
      case Start(_) | End(_) | Keyword("¬") => false
      case _ => true
    }

    val lastIndex = format.last.lastIndexWhere {
      case Start(_) | End(_) => false
      case _ => true
    }

    if headIndex != -1 && lastIndex != -1 then
      (format.head(headIndex), format.last(lastIndex)) match
        case (open, close: Close) if close.opening eq open =>
          if format.lengthCompare(1) > 0 then
            format.head.patch(headIndex, List.empty, 1) :: (format.init.tail :+ format.last.patch(lastIndex, List.empty, 1))
          else
            List(format.head.patch(lastIndex, List.empty, 1).patch(headIndex, List.empty, 1))
        case _ =>
          format
    else
      format

  def start = Start(expr)

  def end = End(expr)

  def mark(format: List[List[Format]]) =
    if format.lengthCompare(1) > 0 then
      (start :: format.head) :: (format.init.tail :+ (format.last :+ end))
    else
      List(start :: (format.head :+ end))

  def formatNested(expr: Term) = expr match
    case Var(_) => expr.format
    case Data(_, args) if args.isEmpty => expr.format
    case _ => parenthesize(expr.format)

  def binaryOp(op: List[Format], a: Term, b: Term) =
    val aOp = formatNested(a)
    val bOp = formatNested(b)
    if aOp.lengthCompare(1) > 0 || bOp.lengthCompare(1) > 0 then
      List(aOp.head) ++ indented(aOp.tail ++ (op :: indented(bOp)))
    else
      List(aOp.head ++ (Plain(" ") :: (op ++ (Plain(" ") :: bOp.head))))

  expr match
    case Cases(a, List(`trueMatch` -> `falseData`, `falseMatch` -> `trueData`)) =>
      val expr = formatNested(a)
      List(start :: Keyword("¬") :: end :: expr.head) ++ expr.tail
    case Cases(a, List(`trueMatch` -> `trueData`, `falseMatch` -> b)) =>
      binaryOp(List(start, Keyword("∨"), end), a, b)
    case Cases(a, List(`trueMatch` -> b, `falseMatch` -> `falseData`)) =>
      binaryOp(List(start, Keyword("∧"), end), a, b)
    case Cases(a, List(`trueMatch` -> b, `falseMatch` -> `trueData`)) =>
      binaryOp(List(start, Keyword("→"), end), a, b)
    case Cases(cond, List(`trueMatch` -> thenBranch, `falseMatch` -> elseBranch)) =>
      val condexpr = formatNested(cond)
      val thenexpr = thenBranch.format
      val elseexpr = elseBranch.format
      val nested = (cond, thenBranch, elseBranch) match
        case (Cases(_, List(`trueMatch` -> _, `falseMatch` -> _)), _, _) => 1
        case (_, Cases(_, List(`trueMatch` -> _, `falseMatch` -> _)), _) => 2
        case (_, _, Cases(_, List(`trueMatch` -> _, `falseMatch` -> _))) => 2
        case _ => 0
      if condexpr.lengthCompare(1) > 0 || nested == 1 then
        mark((Keyword("if") :: Plain(" ") :: condexpr.head) :: (indented(condexpr.tail) ++ (List(Keyword("then")) :: indented(thenexpr)) ++ (List(Keyword("else")) :: indented(elseexpr))))
      else if thenexpr.lengthCompare(1) > 0 || elseexpr.lengthCompare(1) > 0 || nested == 2 then
        mark((Keyword("if") :: Plain(" ") :: (condexpr.head :+ Plain(" ") :+ Keyword("then"))) :: (indented(thenexpr) ++ (List(Keyword("else")) :: indented(elseexpr))))
      else
        mark(List((Keyword("if") :: Plain(" ") :: condexpr.head) ++ (Plain(" ") :: Keyword("then") :: Plain(" ") :: thenexpr.head) ++ (Plain(" ") :: Keyword("else") :: Plain(" ") :: elseexpr.head)))
    case Cases(bound, List(pattern -> expr)) =>
      val letbound = bound.format
      val letexpr = expr.format
      val letpattern = Keyword("let") :: Plain(" ") :: (pattern.format :+ Plain(" ") :+ Keyword("="))
      if letbound.lengthCompare(1) > 0 then
        mark(letpattern :: indented(letbound) ++ (List(Keyword("in")) :: indented(letexpr)))
      else if letexpr.lengthCompare(1) > 0 then
        mark(letpattern ++ (Plain(" ") :: (letbound.head :+ Plain(" ") :+ Keyword("in"))) :: indented(letexpr))
      else
        mark(List(letpattern ++ (Plain(" ") :: (letbound.head ++ (Plain(" ") :: Keyword("in") :: Plain(" ") :: letexpr.head)))))
    case Abs(properties, ident, tpe, expr) =>
      val absexpr = expr.format
      val (absexprproc, dot) = expr match
        case expr: Abs if expr.properties.isEmpty =>
          (absexpr.head.patch(1, List.empty, 2) :: absexpr.tail, List.empty)
        case _ =>
          (absexpr, List(Keyword(".")))
      ((start :: Keyword("λ") :: Plain(" ") :: Plain(s"${annotation(properties)}${ident.name}: ${tpe.show}") :: dot) ++ (end :: Plain(" ") :: absexprproc.head)) :: indented(absexprproc.tail)
    case App(properties, expr, arg) =>
      val format = formatNested(expr)
      val appexpr = expr match
        case _: (App | TypeApp) if properties.isEmpty && format.lengthCompare(1) == 0 =>
          deparenthesize(format)
        case _ =>
          format
      val apparg = formatNested(arg)
      if appexpr.lengthCompare(1) > 0 || apparg.lengthCompare(1) > 0 then
        mark(parenthesize((Plain(annotation(properties)) :: appexpr.head) :: (indented(appexpr.tail) ++ indented(apparg))))
      else
        mark(List(Plain(annotation(properties)) :: (appexpr.head ++ (Plain(" ") :: apparg.head))))
    case TypeAbs(tpe, expr) =>
      val typeabsexpr = expr.format
      val (typeabsexprproc, dot) = expr match
        case expr: TypeAbs =>
          (typeabsexpr.head.patch(1, List.empty, 2) :: typeabsexpr.tail, List.empty)
        case _ =>
          (typeabsexpr, List(Keyword(".")))
      ((start :: Keyword("Λ") :: Plain(" ") :: Plain(tpe.name) :: dot) ++ (end :: Plain(" ") :: typeabsexprproc.head)) :: indented(typeabsexprproc.tail)
    case TypeApp(expr, tpe) =>
      val typeappexpr = expr.format
      (expr, typeappexpr.last.last) match
        case (_: TypeApp, close: Close) =>
          typeappexpr.init :+ (typeappexpr.last.init ++ List(Plain(", "), start, Plain(tpe.show), end, close))
        case _ =>
          val open = Open("[")
          typeappexpr.init :+ (typeappexpr.last ++ List(Plain(" "), open, start, Plain(tpe.show), end, Close("]")(open)))
    case Data(ctor, List()) if ctor == True || ctor == False || (ctor.ident.name.headOption exists { _.isUpper }) =>
      mark(List(List(Plain(ctor.show))))
    case Data(ctor, List()) =>
      mark(parenthesize(List(List(Plain(ctor.show)))))
    case Data(ctor, args) =>
      val dataargss = args map formatNested
      val dataargs = dataargss.flatten
      if dataargss exists { _.lengthCompare(1) > 0 } then
        mark(parenthesize(List(Plain(ctor.show)) :: indented(dataargs)))
      else
        mark(List(Plain(ctor.show) :: (dataargs flatMap { Plain(" ") :: _ })))
    case Var(ident) =>
      mark(List(List(Plain(ident.name))))
    case Cases(scrutinee, cases) =>
      val casesscrutinee = formatNested(scrutinee)
      val caselist = cases map { (pattern, expr) =>
        val caseexpr = expr.format
        (pattern.format ++ (Plain(" ") :: Keyword("⇒") :: Plain(" ") :: caseexpr.head)) :: indented(caseexpr.tail)
      }
      if casesscrutinee.lengthCompare(1) > 0 then
        List(start, Keyword("cases"), end) :: (indented(casesscrutinee) ++ (List(Keyword("of")) :: indented(caselist.flatten)))
      else
        (start :: Keyword("cases") :: end :: Plain(" ") :: (casesscrutinee.head :+ Plain(" ") :+ Keyword("of"))) :: indented(caselist.flatten)
