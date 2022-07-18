package propel
package dsl

import ast.*

extension (property: Property) def show: String = property match
  case Commutative => "comm"
  case Associative => "assoc"
  case Idempotent => "idem"
  case Reflexive => "refl"
  case Irreflexive => "irefl"
  case Symmetric => "sym"
  case Antisymmetric => "antisym"
  case Asymmetric => "asym"
  case Connected => "conn"
  case Transitive => "trans"

extension (properties: Properties) def show: String =
  properties.map(_.show).mkString(", ")

extension (constructor: Constructor) def show: String =
  constructor.ident.name

extension (pattern: Pattern) def show: String = pattern match
  case Match(ctor, List()) if ctor == True || ctor == False || (ctor.ident.name.headOption exists { _.isUpper }) =>
    ctor.ident.name
  case Match(ctor, List()) =>
    s"(${ctor.ident.name})"
  case Match(ctor, args) =>
    s"${ctor.ident.name} ${(args map {
      case arg @ Match(_, args) if args.nonEmpty =>
        val matcharg = arg.show
        if (matcharg startsWith "(") && (matcharg endsWith ")") then matcharg else s"($matcharg)"
      case arg =>
        arg.show
    }).mkString(" ")}"
  case Bind(ident) =>
    ident.name

extension (expr: Term) def show: String =
  def show(expr: Term): List[String] =
    val falseMatch = Match(False, List.empty)
    val falseData = Data(False, List.empty)
    val trueMatch = Match(True, List.empty)
    val trueData = Data(True, List.empty)

    val indent = "  "

    def annotation(properties: Properties) =
      if properties.isEmpty then "" else s"[${properties.show}] "

    def indented(values: List[String]) =
      if values forall { _ startsWith indent } then values else values map { indent + _ }

    def flatten(values: (String | List[String])*) = (values map {
        case value: String => List(value)
        case value: List[String] => value
      }).flatten.toList

    def parenthesize(values: List[String]) =
      if ((values.head startsWith "(") || (values.head startsWith "¬(")) &&
          (values.last endsWith ")") then
        values
      else if values.lengthCompare(1) > 0 then
        flatten(s"(${values.head}", values.init.tail, s"${values.last})")
      else
        flatten(s"(${values.head})")

    def showNested(expr: Term) = expr match
      case Var(_) => show(expr)
      case Data(_, args) if args.isEmpty => show(expr)
      case _ => parenthesize(show(expr))

    def binaryOp(op: String, a: Term, b: Term) =
      val aOp = showNested(a)
      val bOp = showNested(b)
      if aOp.lengthCompare(1) > 0 || bOp.lengthCompare(1) > 0 then
        aOp.head :: indented(flatten(aOp.tail, op, indented(bOp)))
      else
        flatten(s"${aOp.head} $op ${bOp.head}")

    expr match
      case Cases(a, List(`trueMatch` -> `falseData`, `falseMatch` -> `trueData`)) =>
        val expr = showNested(a)
        flatten(s"¬${expr.head}", expr.tail)
      case Cases(a, List(`trueMatch` -> `trueData`, `falseMatch` -> b)) =>
        binaryOp("∨", a, b)
      case Cases(a, List(`trueMatch` -> b, `falseMatch` -> `falseData`)) =>
        binaryOp("∧", a, b)
      case Cases(a, List(`trueMatch` -> b, `falseMatch` -> `trueData`)) =>
        binaryOp("→", a, b)
      case Cases(cond, List(`trueMatch` -> thenBranch, `falseMatch` -> elseBranch)) =>
        val condexpr = showNested(cond)
        val thenexpr = show(thenBranch)
        val elseexpr = show(elseBranch)
        if condexpr.lengthCompare(1) > 0 then
          flatten(s"if ${condexpr.head}", indented(condexpr.tail), "then", indented(thenexpr), "else", indented(elseexpr))
        else if thenexpr.lengthCompare(1) > 0 || elseexpr.lengthCompare(1) > 0 then
          flatten(s"if ${condexpr.head} then", indented(thenexpr), "else", indented(elseexpr))
        else
          flatten(s"if ${condexpr.head} then ${thenexpr.head} else ${elseexpr.head}")
      case App(_, Abs(_, ident0, Cases(Var(ident1), List(pattern -> expr))), bound: (Abs | Cases)) if ident0 == ident1 =>
        val letbound = show(bound)
        flatten(s"let ${pattern.show} = ${letbound.head}", indented(letbound.tail), "in", indented(show(expr)))
      case App(_, Abs(_, ident0, Cases(Var(ident1), List(pattern -> expr))), bound) if ident0 == ident1 =>
        val letbound = show(bound)
        val letexpr = show(expr)
        if letbound.lengthCompare(1) > 0 then
          flatten(s"let ${pattern.show} =", indented(letbound), "in", indented(letexpr))
        else if letexpr.lengthCompare(1) > 0 then
          flatten(s"let ${pattern.show} = ${letbound.head} in", indented(letexpr))
        else
          flatten(s"let ${pattern.show} = ${letbound.head} in ${letexpr.head}")
      case Abs(properties, arg, expr) =>
        val absexpr = show(expr)
        val absexprproc = expr match
          case expr: Abs if expr.properties.isEmpty => flatten(s" ${absexpr.head.drop(2)}", absexpr.tail)
          case _ => flatten(s". ${absexpr.head}", absexpr.tail)
        flatten(s"λ ${annotation(properties)}${arg.name}${absexprproc.head}", indented(absexprproc.tail))
      case Data(ctor, List()) if ctor == True || ctor == False || (ctor.ident.name.headOption exists { _.isUpper }) =>
        flatten(ctor.show)
      case Data(ctor, List()) =>
        parenthesize(flatten(ctor.show))
      case Data(ctor, args) =>
        val dataargss = args map showNested
        val dataargs = dataargss.flatten
        if dataargss exists { _.lengthCompare(1) > 0 } then
          parenthesize(flatten(s"${ctor.show}", indented(dataargs)))
        else
          flatten(s"${ctor.show} ${dataargs.mkString(" ")}")
      case App(properties, expr, arg) =>
        val appexpr = expr match
          case _: App if properties.isEmpty =>
            val values = showNested(expr)
            if values.lengthCompare(1) == 0 &&
                ((values.head startsWith "(") || (values.head startsWith "¬(")) &&
                (values.last endsWith ")") then
              flatten(values.head.drop(1).dropRight(1))
            else
              values
          case _ =>
            showNested(expr)
        val apparg = showNested(arg)
        if appexpr.lengthCompare(1) > 0 || apparg.lengthCompare(1) > 0 then
          parenthesize(flatten(s"${annotation(properties)}${appexpr.head}", indented(appexpr.tail), indented(apparg)))
        else
          flatten(s"${annotation(properties)}${appexpr.mkString(" ")} ${apparg.mkString(" ")}")
      case Var(ident) =>
        flatten(ident.name)
      case Cases(scrutinee, cases) =>
        val casesscrutinee = showNested(scrutinee)
        val caselist = cases map { (pattern, expr) =>
          val caseexpr = show(expr)
          flatten(s"${pattern.show} ⇒ ${caseexpr.head}", indented(caseexpr.tail))
        }
        if casesscrutinee.lengthCompare(1) > 0 then
          flatten("cases", indented(casesscrutinee), "of", indented(caselist.flatten))
        else
          flatten(s"cases ${casesscrutinee.head} of", indented(caselist.flatten))

  show(expr).mkString("\n")
