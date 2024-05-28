package propel

import scala.io.Source
import scala.util.{Success, Using, Failure}
import java.io.IOException
import scala.scalajs.js.annotation._


object defaults:
  import ast.Property.*

  val error = Option.empty[String]
  val content = Option.empty[String | ast.Term]
  val deduction = false
  val reduction = false
  val discoverAlgebraicProperties = true
  val disableEqualities = false
  val disableInequalities = false
  val ignorePosContradiction = false
  val ignoreNegContradiction = false
  val ignorePosNegContradiction = false
  val ignoreCyclicContradiction = false
  val maxNumberOfLemmas = -1
  val maxNumberOfFacts = -1
  val runMain = false
  val keepRewritesBits = 8
  val propertiesOrder = List(
    Reflexive, Irreflexive, Antisymmetric, Symmetric, Connected, Transitive,
    Commutative, Selection, Idempotent, Associative)


@main def check(arguments: String*) =
  def parsedArguments =
    import ast.Property.*

    var error = defaults.error
    var content = defaults.content
    var deduction = defaults.deduction
    var reduction = defaults.reduction
    var discoverAlgebraicProperties = defaults.discoverAlgebraicProperties
    var disableEqualities = defaults.disableEqualities
    var disableInequalities = defaults.disableInequalities
    var ignorePosContradiction = defaults.ignorePosContradiction
    var ignoreNegContradiction = defaults.ignoreNegContradiction
    var ignorePosNegContradiction = defaults.ignorePosNegContradiction
    var ignoreCyclicContradiction = defaults.ignoreCyclicContradiction
    var maxNumberOfLemmas = defaults.maxNumberOfLemmas
    var maxNumberOfFacts = defaults.maxNumberOfFacts
    var runMain = defaults.runMain
    var keepRewritesBits = defaults.keepRewritesBits
    var propertiesOrder = defaults.propertiesOrder

    if arguments.size > 0 && arguments.head != "-h" && arguments.head != "--help" then
      val args = arguments.iterator
      while args.hasNext && error.isEmpty do
        args.next() match
          case "-f" | "--file" =>
            if args.hasNext then
              try content = Some(Using.resource(Source.fromFile(args.next()))(_.mkString))
              catch case exception: IOException => error = Some(exception.getMessage.nn)
            else
              error = Some("No input file specified")
          case "-c" | "--content" =>
            if args.hasNext then
              content = Some(args.next())
            else
              error = Some("No input specified on the command line")
          case "-i" | "--stdin" =>
            content = Some(Source.stdin.mkString)
          case "--runMain" =>
            runMain = true
          case "-b" | "--built-in" =>
            if args.hasNext then
              try content = Some(builtInBenchmarks(args.next()))
              catch case exception: IOException => error = Some(exception.getMessage.nn)
            else
              error = Some("No built-in benchmark specified on the command line")
          case "-d" | "--print-deduction" =>
            deduction = true
          case "-r" | "--print-reduction" =>
            reduction = true
          case "--no-prop-discovery" =>
            discoverAlgebraicProperties = false
          case "--no-eq" =>
            disableEqualities = true
          case "--no-ineq" =>
            disableInequalities = true
          case "--ignore-contra-eq" =>
            ignorePosContradiction = true
          case "--ignore-contra-ineq" =>
            ignoreNegContradiction = true
          case "--ignore-contra-eq-ineq" =>
            ignorePosNegContradiction = true
          case "--ignore-contra-cycle" =>
            ignoreCyclicContradiction = true
          case "--keep-rewrites" =>
            if args.hasNext then
              try
                val number = args.next().toInt
                if Integer.bitCount(number) != 1 then error = Some("Number needs to be a power of two")
                else keepRewritesBits = 31 - Integer.numberOfLeadingZeros(number)
              catch case exception: NumberFormatException => error = Some(exception.getMessage.nn)
            else
              error = Some("No number given")
          case "--prop-order" =>
            if args.hasNext then
              val properties = args.next().split(',').toList flatMap {
                case "comm" => Some(Commutative)
                case "assoc" => Some(Associative)
                case "idem" => Some(Idempotent)
                case "sel" => Some(Selection)
                case "refl" => Some(Reflexive)
                case "irefl" => Some(Irreflexive)
                case "sym" => Some(Symmetric)
                case "antisym" => Some(Antisymmetric)
                case "asym" => Some(Asymmetric)
                case "conn" => Some(Connected)
                case "trans" => Some(Transitive)
                case prop =>
                  error = Some(s"Invalid property: $prop")
                  None
              }
              if error.isEmpty then
                propertiesOrder = properties
            else
              error = Some("No properties given")
          case "--max-lemmas" =>
            if args.hasNext then
              try
                maxNumberOfLemmas = args.next().toInt
              catch case exception: NumberFormatException => error = Some(exception.getMessage.nn)
            else
            error = Some("No number given")
          case "--max-facts" =>
            if args.hasNext then
              try
                maxNumberOfFacts = args.next().toInt
              catch case exception: NumberFormatException => error = Some(exception.getMessage.nn)
            else
            error = Some("No number given")
          case arg =>
            error = Some(s"Unknown option: $arg")

    (error, content, deduction, reduction, discoverAlgebraicProperties,
     disableEqualities, disableInequalities,
     ignorePosContradiction, ignoreNegContradiction,
     ignorePosNegContradiction, ignoreCyclicContradiction, runMain,
     keepRewritesBits, propertiesOrder, maxNumberOfLemmas, maxNumberOfFacts)

  parsedArguments match
    case (Some(error), _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) =>
      println(s"Error: $error")

    case (_, None, _, _, _, _, _, _, _, _, _, _, _, _, _, _) =>
      println("Usage: propel [ARGUMENT]...")
      println("Verifies the algebraic and relational properties of functions specified in Propel's input format.")
      println()
      println("Specifying one of the following arguments is required.")
      println("  -c CONTENT, --content CONTENT    use the input specified on the command line")
      println("  -f FILE, --file FILE             read the input from the specified file")
      println("  -i, --stdin                      read the input from standard input")
      println("  --runMain                        print the value that the main function evaluates to")
      println("  -b NAME, --built-in NAME         built-in benchmark")
      println()
      println("Specifying the following arguments is optional.")
      println("  -d, --print-deduction            print deduced properties")
      println("  -r, --print-reduction            print reduced expressions")
      println("      --no-prop-discovery          disable discovery of algebraic properties")
      println("      --no-eq                      disable equality set")
      println("      --no-ineq                    disable inequality set")
      println("      --ignore-contra-eq           ignore contradiction in equalities")
      println("      --ignore-contra-ineq         ignore contradiction in inequalities")
      println("      --ignore-contra-eq-ineq      ignore contradiction across in/equalities")
      println("      --ignore-contra-cycle        ignore contradiction through cycles")
      println("      --max-lemmas NUMBER          generate a limited number of lemmas")
      println("      --max-facts NUMBER           generate a limited number of facts")
      println("      --keep-rewrites NUMBER       number of top-scored rewrites to keep")
      println("      --prop-order PROPERTIES      comma-separated list of properties")

    case (_, Some(content), deduction, reduction, discoverAlgebraicProperties,
          disableEqualities, disableInequalities,
          ignorePosContradiction, ignoreNegContradiction,
          ignorePosNegContradiction, ignoreCyclicContradiction, runMain,
          keepRewritesBits, propertiesOrder, maxNumberOfLemmas, maxNumberOfFacts) =>
      parseAndCheckSourceCode(
        content, deduction, reduction, discoverAlgebraicProperties,
        disableEqualities, disableInequalities,
        ignorePosContradiction, ignoreNegContradiction,
        ignorePosNegContradiction, ignoreCyclicContradiction, runMain,
        keepRewritesBits, propertiesOrder, maxNumberOfLemmas, maxNumberOfFacts)


@JSExportTopLevel("parseAndCheckSourceCode")
def parseAndCheckSourceCode(
    code: String | ast.Term,
    deduction: Boolean = defaults.deduction,
    reduction: Boolean = defaults.reduction,
    discoverAlgebraicProperties: Boolean = defaults.discoverAlgebraicProperties,
    disableEqualities: Boolean = defaults.disableEqualities,
    disableInequalities: Boolean = defaults.disableInequalities,
    ignorePosContradiction: Boolean = defaults.ignorePosContradiction,
    ignoreNegContradiction: Boolean = defaults.ignoreNegContradiction,
    ignorePosNegContradiction: Boolean = defaults.ignorePosNegContradiction,
    ignoreCyclicContradiction: Boolean = defaults.ignoreCyclicContradiction,
    runMain: Boolean = defaults.runMain,
    keepRewritesBits: Int = defaults.keepRewritesBits,
    propertiesOrder: List[ast.Property] = defaults.propertiesOrder,
    maxNumberOfLemmas: Int = defaults.maxNumberOfLemmas,
    maxNumberOfFacts: Int = defaults.maxNumberOfFacts) =
  val exprToEval = if runMain
                   then ast.Var(Symbol("main"))
                   else ast.Data(ast.Constructor(Symbol("Unit")), List.empty)
  val expr = code match
    case v: String => parser.deserializeWithExpr(v, exprToEval)
    case v: ast.Term => Success(v)
  if runMain
  then expr match
        case Success(e) => println(printing.show(evaluator.Concrete.eval(e)))
        case Failure(e) => println(e)
  else
    expr.fold(
      exception =>
        println(s"Error: ${exception.getMessage}"),

      expr =>
        evaluator.Equalities.debugDisableEqualities = disableEqualities
        evaluator.Equalities.debugDisableInequalities = disableInequalities
        evaluator.Equalities.debugIgnorePosContradiction = ignorePosContradiction
        evaluator.Equalities.debugIgnoreNegContradiction = ignoreNegContradiction
        evaluator.Equalities.debugIgnorePosNegContradiction = ignorePosNegContradiction
        evaluator.Equalities.debugIgnoreCyclicContradiction = ignoreCyclicContradiction
        evaluator.properties.debugMaxKeepRewriteNumberBits = keepRewritesBits
        evaluator.properties.debugPropertiesOrder = propertiesOrder

        val term = evaluator.properties.check(expr,
          discoverAlgebraicProperties = discoverAlgebraicProperties,
          printDeductionDebugInfo = deduction,
          printReductionDebugInfo = reduction,
          maxNumberOfLemmas = maxNumberOfLemmas,
          maxNumberOfFacts = maxNumberOfFacts)

        if deduction || reduction then
          println()

        val errors = printing.showErrors(term)
        if errors.isEmpty then
          println("✔ Check successful.")
        else
          println(errors)
          println("✘ Check failed."))


extension (expr: ast.Term)
  def withCustomProperty(pattern: ast.Term, result: ast.Term, variables: Set[Symbol], abstraction: Symbol) =
    evaluator.properties.addCustomProperty(pattern, result, variables, abstraction, expr)

val builtInBenchmarks = Map(
  "nat_add1_comm" ->
  parser.deserialize("""
    (letrec nat_add1 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add1 x y))]))
      Unit)
  """).get,

  "nat_add1_assoc" ->
  parser.deserialize("""
    (letrec nat_add1 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add1 x y))]))
      Unit)
  """).get,

  "nat_add1_leftid" ->
  parser.deserialize("""
    (letrec nat_add1 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add1 x y))]))
      Unit)
  """).get.withCustomProperty(
    parser.deserialize("(nat_add1 Z x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("nat_add1")),

  "nat_add1_rightid" ->
  parser.deserialize("""
    (letrec nat_add1 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add1 x y))]))
      Unit)
  """).get.withCustomProperty(
    parser.deserialize("(nat_add1 x Z)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("nat_add1")),

  "nat_add2_comm" ->
  parser.deserialize("""
    (letrec nat_add2 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add2 y x))]))
      Unit)
  """).get,

  "nat_add2_assoc" ->
  parser.deserialize("""
    (letrec nat_add2 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add2 y x))]))
      Unit)
  """).get,

  "nat_add2_leftid" ->
  parser.deserialize("""
    (letrec nat_add2 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add2 y x))]))
      Unit)
  """).get.withCustomProperty(
    parser.deserialize("(nat_add2 Z x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("nat_add2")),

  "nat_add2_rightid" ->
  parser.deserialize("""
    (letrec nat_add2 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add2 y x))]))
      Unit)
  """).get.withCustomProperty(
    parser.deserialize("(nat_add2 x Z)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("nat_add2")),

  "nat_add3_comm" ->
  parser.deserialize("""
    (letrec nat_add3 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) y]
        [(Tuple x Z) x]
        [(Tuple (S x) (S y)) (S (S (nat_add3 x y)))]))
      Unit)
  """).get,

  "nat_add3_assoc" ->
  parser.deserialize("""
    (letrec nat_add3 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) y]
        [(Tuple x Z) x]
        [(Tuple (S x) (S y)) (S (S (nat_add3 x y)))]))
      Unit)
  """).get,

  "nat_add3_leftid" ->
  parser.deserialize("""
    (letrec nat_add3 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) y]
        [(Tuple x Z) x]
        [(Tuple (S x) (S y)) (S (S (nat_add3 x y)))]))
      Unit)
  """).get.withCustomProperty(
    parser.deserialize("(nat_add3 Z x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("nat_add3")),

  "nat_add3_rightid" ->
  parser.deserialize("""
    (letrec nat_add3 (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) y]
        [(Tuple x Z) x]
        [(Tuple (S x) (S y)) (S (S (nat_add3 x y)))]))
      Unit)
  """).get.withCustomProperty(
    parser.deserialize("(nat_add3 x Z)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("nat_add3")),

  "nat_mult_comm" ->
  parser.deserialize("""
    (letrec nat_add (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add x y))]))
      (letrec nat_mult (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S x) (nat_add y (nat_mult x y))]))
        Unit))
  """).get,

  "nat_mult_assoc" ->
  parser.deserialize("""
    (letrec nat_add (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add x y))]))
      (letrec nat_mult (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S x) (nat_add y (nat_mult x y))]))
        Unit))
  """).get,

  "nat_mult_leftid" ->
  parser.deserialize("""
    (letrec nat_add (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add x y))]))
      (letrec nat_mult (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S x) (nat_add y (nat_mult x y))]))
        Unit))
  """).get.withCustomProperty(
    parser.deserialize("(nat_mult (S Z) x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("nat_mult")),

  "nat_mult_rightid" ->
  parser.deserialize("""
    (letrec nat_add (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S x) (S (nat_add x y))]))
      (letrec nat_mult (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S x) (nat_add y (nat_mult x y))]))
        Unit))
  """).get.withCustomProperty(
    parser.deserialize("(nat_mult x (S Z))").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("nat_mult")),

  "nat_min_comm" ->
  parser.deserialize("""
    (letrec nat_min (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) Z]
        [(Tuple x Z) Z]
        [(Tuple (S x) (S y)) (S (nat_min x y))]))
      Unit)
  """).get,

  "nat_min_assoc" ->
  parser.deserialize("""
    (letrec nat_min (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) Z]
        [(Tuple x Z) Z]
        [(Tuple (S x) (S y)) (S (nat_min x y))]))
      Unit)
  """).get,

  "nat_min_idem" ->
  parser.deserialize("""
    (letrec nat_min (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [idem] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) Z]
        [(Tuple x Z) Z]
        [(Tuple (S x) (S y)) (S (nat_min x y))]))
      Unit)
  """).get,

  "nat_min_sel" ->
  parser.deserialize("""
    (letrec nat_min (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [sel] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) Z]
        [(Tuple x Z) Z]
        [(Tuple (S x) (S y)) (S (nat_min x y))]))
      Unit)
  """).get,

  "nat_max_comm" ->
  parser.deserialize("""
    (letrec nat_max (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) y]
        [(Tuple x Z) x]
        [(Tuple (S x) (S y)) (S (nat_max x y))]))
      Unit)
  """).get,

  "nat_max_assoc" ->
  parser.deserialize("""
    (letrec nat_max (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) y]
        [(Tuple x Z) x]
        [(Tuple (S x) (S y)) (S (nat_max x y))]))
      Unit)
  """).get,

  "nat_max_idem" ->
  parser.deserialize("""
    (letrec nat_max (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [idem] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) y]
        [(Tuple x Z) x]
        [(Tuple (S x) (S y)) (S (nat_max x y))]))
      Unit)
  """).get,

  "nat_max_sel" ->
  parser.deserialize("""
    (letrec nat_max (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [sel] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) y]
        [(Tuple x Z) x]
        [(Tuple (S x) (S y)) (S (nat_max x y))]))
      Unit)
  """).get,

  "nat_max_leftid" ->
  parser.deserialize("""
    (letrec nat_max (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) y]
        [(Tuple x Z) x]
        [(Tuple (S x) (S y)) (S (nat_max x y))]))
      Unit)
  """).get.withCustomProperty(
    parser.deserialize("(nat_max Z x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("nat_max")),

  "nat_max_rightid" ->
  parser.deserialize("""
    (letrec nat_max (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases (Tuple x y)
        [(Tuple Z y) y]
        [(Tuple x Z) x]
        [(Tuple (S x) (S y)) (S (nat_max x y))]))
      Unit)
  """).get.withCustomProperty(
    parser.deserialize("(nat_max x Z)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("nat_max")),

  "bv_add_comm" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ (B1 BZ)]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_add (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [comm] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ BZ) BZ]
          [(Tuple BZ (B0 y)) (B0 y)]
          [(Tuple BZ (B1 y)) (B1 y)]
          [(Tuple (B0 x) BZ) (B0 x)]
          [(Tuple (B1 x) BZ) (B1 x)]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_add x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_add x y)))]))
        Unit))
  """).get,

  "bv_add_assoc" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ (B1 BZ)]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_add (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [assoc] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ BZ) BZ]
          [(Tuple BZ (B0 y)) (B0 y)]
          [(Tuple BZ (B1 y)) (B1 y)]
          [(Tuple (B0 x) BZ) (B0 x)]
          [(Tuple (B1 x) BZ) (B1 x)]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_add x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_add x y)))]))
        Unit))
  """).get,

  "bv_add_leftid" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ (B1 BZ)]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_add (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ BZ) BZ]
          [(Tuple BZ (B0 y)) (B0 y)]
          [(Tuple BZ (B1 y)) (B1 y)]
          [(Tuple (B0 x) BZ) (B0 x)]
          [(Tuple (B1 x) BZ) (B1 x)]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_add x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_add x y)))]))
        Unit))
  """).get.withCustomProperty(
    parser.deserialize("(bv_add BZ x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("bv_add")),

  "bv_add_rightid" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ (B1 BZ)]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_add (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ BZ) BZ]
          [(Tuple BZ (B0 y)) (B0 y)]
          [(Tuple BZ (B1 y)) (B1 y)]
          [(Tuple (B0 x) BZ) (B0 x)]
          [(Tuple (B1 x) BZ) (B1 x)]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_add x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_add x y)))]))
        Unit))
  """).get.withCustomProperty(
    parser.deserialize("(bv_add BZ x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("bv_add")),

  "bv_mult_comm" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ (B1 BZ)]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_add (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ BZ) BZ]
          [(Tuple BZ (B0 y)) (B0 y)]
          [(Tuple BZ (B1 y)) (B1 y)]
          [(Tuple (B0 x) BZ) (B0 x)]
          [(Tuple (B1 x) BZ) (B1 x)]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_add x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_add x y)))]))
        (letrec bv_mult (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
          (lambda [comm] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ}))
            (cases (Pair x y)
              [(Pair _ BZ) BZ]
              [(Pair BZ _) BZ]
              [(Pair (B0 x) y) (B0 (bv_mult x y))]
              [(Pair (B1 x) y) (bv_add y (B0 (bv_mult x y)))]))
          Unit)))
  """).get,

  "bv_mult_assoc" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ (B1 BZ)]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_add (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ BZ) BZ]
          [(Tuple BZ (B0 y)) (B0 y)]
          [(Tuple BZ (B1 y)) (B1 y)]
          [(Tuple (B0 x) BZ) (B0 x)]
          [(Tuple (B1 x) BZ) (B1 x)]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_add x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_add x y)))]))
        (letrec bv_mult (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
          (lambda [assoc] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ}))
            (cases (Pair x y)
              [(Pair _ BZ) BZ]
              [(Pair BZ _) BZ]
              [(Pair (B0 x) y) (B0 (bv_mult x y))]
              [(Pair (B1 x) y) (bv_add y (B0 (bv_mult x y)))]))
          Unit)))
  """).get,

  "bv_mult_leftid" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ (B1 BZ)]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_add (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ BZ) BZ]
          [(Tuple BZ (B0 y)) (B0 y)]
          [(Tuple BZ (B1 y)) (B1 y)]
          [(Tuple (B0 x) BZ) (B0 x)]
          [(Tuple (B1 x) BZ) (B1 x)]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_add x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_add x y)))]))
        (letrec bv_mult (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
          (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ}))
            (cases (Pair x y)
              [(Pair _ BZ) BZ]
              [(Pair BZ _) BZ]
              [(Pair (B0 x) y) (B0 (bv_mult x y))]
              [(Pair (B1 x) y) (bv_add y (B0 (bv_mult x y)))]))
          Unit)))
  """).get.withCustomProperty(
    parser.deserialize("(bv_mult (B1 BZ) x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("bv_mult")),

  "bv_mult_rightid" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ (B1 BZ)]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_add (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ BZ) BZ]
          [(Tuple BZ (B0 y)) (B0 y)]
          [(Tuple BZ (B1 y)) (B1 y)]
          [(Tuple (B0 x) BZ) (B0 x)]
          [(Tuple (B1 x) BZ) (B1 x)]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_add x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_add x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_add x y)))]))
        (letrec bv_mult (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
          (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ}))
            (cases (Pair x y)
              [(Pair _ BZ) BZ]
              [(Pair BZ _) BZ]
              [(Pair (B0 x) y) (B0 (bv_mult x y))]
              [(Pair (B1 x) y) (bv_add y (B0 (bv_mult x y)))]))
          Unit)))
  """).get.withCustomProperty(
    parser.deserialize("(bv_mult x (B1 BZ))").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("bv_mult")),

  "bv_addmod_comm" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ BZ]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_addmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [comm] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_addmod x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_addmod x y)))]))
        Unit))
  """).get,

  "bv_addmod_assoc" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ BZ]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_addmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [assoc] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_addmod x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_addmod x y)))]))
        Unit))
  """).get,

  "bv_addmod_leftid" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ BZ]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_addmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_addmod x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_addmod x y)))]))
        Unit))
  """).get.withCustomProperty(
    parser.deserialize("(bv_addmod BZ x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("bv_addmod")),

  "bv_addmod_rightid" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ BZ]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_addmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_addmod x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_addmod x y)))]))
        Unit))
  """).get.withCustomProperty(
    parser.deserialize("(bv_addmod BZ x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("bv_addmod")),

  "bv_multmod_comm" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ BZ]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_addmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_addmod x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_addmod x y)))]))
        (letrec bv_multmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
          (lambda [comm] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ}))
            (cases (Pair x y)
              [(Pair _ BZ) BZ]
              [(Pair BZ _) BZ]
              [(Pair (B0 x) y) (B0 (bv_multmod x y))]
              [(Pair (B1 x) y) (bv_addmod y (B0 (bv_multmod x y)))]))
          Unit)))
  """).get,

  "bv_multmod_assoc" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ BZ]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_addmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_addmod x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_addmod x y)))]))
        (letrec bv_multmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
          (lambda [assoc] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ}))
            (cases (Pair x y)
              [(Pair _ BZ) BZ]
              [(Pair BZ _) BZ]
              [(Pair (B0 x) y) (B0 (bv_multmod x y))]
              [(Pair (B1 x) y) (bv_addmod y (B0 (bv_multmod x y)))]))
          Unit)))
  """).get,

  "bv_multmod_leftid" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ BZ]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_addmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_addmod x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_addmod x y)))]))
        (letrec bv_multmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
          (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ}))
            (cases (Pair x y)
              [(Pair _ BZ) BZ]
              [(Pair BZ _) BZ]
              [(Pair (B0 x) y) (B0 (bv_multmod x y))]
              [(Pair (B1 x) y) (bv_addmod y (B0 (bv_multmod x y)))]))
          Unit)))
  """).get.withCustomProperty(
    parser.deserialize("(bv_multmod (B1 BZ) x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("bv_multmod")),

  "bv_multmod_rightid" ->
  parser.deserialize("""
    (letrec bv_succ (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (cases x
        [BZ BZ]
        [(B0 x) (B1 x)]
        [(B1 x) (B0 (bv_succ x))]))
      (letrec bv_addmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_addmod x y))]
          [(Tuple (B0 x) (B1 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B0 y)) (B1 (bv_addmod x y))]
          [(Tuple (B1 x) (B1 y)) (B0 (bv_succ (bv_addmod x y)))]))
        (letrec bv_multmod (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
          (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ}))
            (cases (Pair x y)
              [(Pair _ BZ) BZ]
              [(Pair BZ _) BZ]
              [(Pair (B0 x) y) (B0 (bv_multmod x y))]
              [(Pair (B1 x) y) (bv_addmod y (B0 (bv_multmod x y)))]))
          Unit)))
  """).get.withCustomProperty(
    parser.deserialize("(bv_multmod x (B1 BZ))").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("bv_multmod")),

  "bv_min_comm" ->
  parser.deserialize("""
    (letrec bv_eq (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) {True False})
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
        [(Tuple BZ BZ) True]
        [(Tuple (B0 x) (B0 y)) (bv_eq x y)]
        [(Tuple (B1 x) (B1 y)) (bv_eq x y)]
        [_ False]))
      (letrec bv_min (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [comm] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_min x y))]
          [(Tuple (B1 x) (B1 y)) (B1 (bv_min x y))]
          [(Tuple (B0 x) (B1 y))
            (if (bv_eq (bv_min x y) y)
              (B1 y)
              (B0 x))]
          [(Tuple (B1 x) (B0 y))
            (if (bv_eq (bv_min x y) x)
              (B1 x)
              (B0 y))]))
        Unit))
  """).get,

  "bv_min_assoc" ->
  parser.deserialize("""
    (letrec bv_eq (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) {True False})
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
        [(Tuple BZ BZ) True]
        [(Tuple (B0 x) (B0 y)) (bv_eq x y)]
        [(Tuple (B1 x) (B1 y)) (bv_eq x y)]
        [_ False]))
      (letrec bv_min (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [assoc] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_min x y))]
          [(Tuple (B1 x) (B1 y)) (B1 (bv_min x y))]
          [(Tuple (B0 x) (B1 y))
            (if (bv_eq (bv_min x y) y)
              (B1 y)
              (B0 x))]
          [(Tuple (B1 x) (B0 y))
            (if (bv_eq (bv_min x y) x)
              (B1 x)
              (B0 y))]))
        Unit))
  """).get,

  "bv_min_idem" ->
  parser.deserialize("""
    (letrec bv_eq (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) {True False})
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
        [(Tuple BZ BZ) True]
        [(Tuple (B0 x) (B0 y)) (bv_eq x y)]
        [(Tuple (B1 x) (B1 y)) (bv_eq x y)]
        [_ False]))
      (letrec bv_min (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [idem] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_min x y))]
          [(Tuple (B1 x) (B1 y)) (B1 (bv_min x y))]
          [(Tuple (B0 x) (B1 y))
            (if (bv_eq (bv_min x y) y)
              (B1 y)
              (B0 x))]
          [(Tuple (B1 x) (B0 y))
            (if (bv_eq (bv_min x y) x)
              (B1 x)
              (B0 y))]))
        Unit))
  """).get,

  "bv_min_sel" ->
  parser.deserialize("""
    (letrec bv_eq (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) {True False})
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
        [(Tuple BZ BZ) True]
        [(Tuple (B0 x) (B0 y)) (bv_eq x y)]
        [(Tuple (B1 x) (B1 y)) (bv_eq x y)]
        [_ False]))
      (letrec bv_min (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [sel] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ _) BZ]
          [(Tuple _ BZ) BZ]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_min x y))]
          [(Tuple (B1 x) (B1 y)) (B1 (bv_min x y))]
          [(Tuple (B0 x) (B1 y))
            (if (bv_eq (bv_min x y) y)
              (B1 y)
              (B0 x))]
          [(Tuple (B1 x) (B0 y))
            (if (bv_eq (bv_min x y) x)
              (B1 x)
              (B0 y))]))
        Unit))
  """).get,

  "bv_max_comm" ->
  parser.deserialize("""
    (letrec bv_eq (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) {True False})
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
        [(Tuple BZ BZ) True]
        [(Tuple (B0 x) (B0 y)) (bv_eq x y)]
        [(Tuple (B1 x) (B1 y)) (bv_eq x y)]
        [_ False]))
      (letrec bv_max (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [comm] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ y) y]
          [(Tuple x BZ) x]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_max x y))]
          [(Tuple (B1 x) (B1 y)) (B1 (bv_max x y))]
          [(Tuple (B0 x) (B1 y))
            (if (bv_eq (bv_max x y) y)
              (B1 y)
              (B0 x))]
          [(Tuple (B1 x) (B0 y))
            (if (bv_eq (bv_max x y) x)
              (B1 x)
              (B0 y))]))
        Unit))
  """).get,

  "bv_max_assoc" ->
  parser.deserialize("""
    (letrec bv_eq (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) {True False})
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
        [(Tuple BZ BZ) True]
        [(Tuple (B0 x) (B0 y)) (bv_eq x y)]
        [(Tuple (B1 x) (B1 y)) (bv_eq x y)]
        [_ False]))
      (letrec bv_max (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [assoc] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ y) y]
          [(Tuple x BZ) x]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_max x y))]
          [(Tuple (B1 x) (B1 y)) (B1 (bv_max x y))]
          [(Tuple (B0 x) (B1 y))
            (if (bv_eq (bv_max x y) y)
              (B1 y)
              (B0 x))]
          [(Tuple (B1 x) (B0 y))
            (if (bv_eq (bv_max x y) x)
              (B1 x)
              (B0 y))]))
        Unit))
  """).get,

  "bv_max_idem" ->
  parser.deserialize("""
    (letrec bv_eq (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) {True False})
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
        [(Tuple BZ BZ) True]
        [(Tuple (B0 x) (B0 y)) (bv_eq x y)]
        [(Tuple (B1 x) (B1 y)) (bv_eq x y)]
        [_ False]))
      (letrec bv_max (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [idem] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ y) y]
          [(Tuple x BZ) x]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_max x y))]
          [(Tuple (B1 x) (B1 y)) (B1 (bv_max x y))]
          [(Tuple (B0 x) (B1 y))
            (if (bv_eq (bv_max x y) y)
              (B1 y)
              (B0 x))]
          [(Tuple (B1 x) (B0 y))
            (if (bv_eq (bv_max x y) x)
              (B1 x)
              (B0 y))]))
        Unit))
  """).get,

  "bv_max_sel" ->
  parser.deserialize("""
    (letrec bv_eq (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) {True False})
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
        [(Tuple BZ BZ) True]
        [(Tuple (B0 x) (B0 y)) (bv_eq x y)]
        [(Tuple (B1 x) (B1 y)) (bv_eq x y)]
        [_ False]))
      (letrec bv_max (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda [sel] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ y) y]
          [(Tuple x BZ) x]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_max x y))]
          [(Tuple (B1 x) (B1 y)) (B1 (bv_max x y))]
          [(Tuple (B0 x) (B1 y))
            (if (bv_eq (bv_max x y) y)
              (B1 y)
              (B0 x))]
          [(Tuple (B1 x) (B0 y))
            (if (bv_eq (bv_max x y) x)
              (B1 x)
              (B0 y))]))
        Unit))
  """).get,

  "bv_max_leftid" ->
  parser.deserialize("""
    (letrec bv_eq (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) {True False})
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
        [(Tuple BZ BZ) True]
        [(Tuple (B0 x) (B0 y)) (bv_eq x y)]
        [(Tuple (B1 x) (B1 y)) (bv_eq x y)]
        [_ False]))
      (letrec bv_max (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ y) y]
          [(Tuple x BZ) x]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_max x y))]
          [(Tuple (B1 x) (B1 y)) (B1 (bv_max x y))]
          [(Tuple (B0 x) (B1 y))
            (if (bv_eq (bv_max x y) y)
              (B1 y)
              (B0 x))]
          [(Tuple (B1 x) (B0 y))
            (if (bv_eq (bv_max x y) x)
              (B1 x)
              (B0 y))]))
        Unit))
  """).get.withCustomProperty(
    parser.deserialize("(bv_max BZ x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("bv_max")),

  "bv_max_rightid" ->
  parser.deserialize("""
    (letrec bv_eq (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) {True False})
      (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
        [(Tuple BZ BZ) True]
        [(Tuple (B0 x) (B0 y)) (bv_eq x y)]
        [(Tuple (B1 x) (B1 y)) (bv_eq x y)]
        [_ False]))
      (letrec bv_max (fun (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}) (rec X {(B0 X) (B1 X) BZ}))
        (lambda (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
          [(Tuple BZ y) y]
          [(Tuple x BZ) x]
          [(Tuple (B0 x) (B0 y)) (B0 (bv_max x y))]
          [(Tuple (B1 x) (B1 y)) (B1 (bv_max x y))]
          [(Tuple (B0 x) (B1 y))
            (if (bv_eq (bv_max x y) y)
              (B1 y)
              (B0 x))]
          [(Tuple (B1 x) (B0 y))
            (if (bv_eq (bv_max x y) x)
              (B1 x)
              (B0 y))]))
        Unit))
  """).get.withCustomProperty(
    parser.deserialize("(bv_max x BZ)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("bv_max")),

  "maybe_functor_id" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type maybe {Nothing (Just nat)})

    (def fmap (fun (fun nat nat) maybe maybe)
      (lambda (f (fun nat nat)) (x maybe)
        (cases x
          [Nothing Nothing]
          [(Just x) (Just (f x))])))
  """).get.withCustomProperty(
    parser.deserialize("(fmap (lambda (y nat) y) x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("fmap")),

  "maybe_functor_composition" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type maybe {Nothing (Just nat)})

    (def fmap (fun (fun nat nat) maybe maybe)
      (lambda (f (fun nat nat)) (x maybe)
        (cases x
          [Nothing Nothing]
          [(Just x) (Just (f x))])))
  """).get.withCustomProperty(
    parser.deserialize("(fmap (lambda (y nat) (f (g y))) x)").get,
    parser.deserialize("(fmap f (fmap g x))").get,
    Set(Symbol("f"), Symbol("g"), Symbol("x")),
    Symbol("fmap")),

  "maybe_semigroup_assoc" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type maybe {Nothing (Just nat)})

    (def nat_add (fun nat nat nat)
      (lambda (x nat) (y nat) (cases x
        [Z y]
        [(S x) (S (nat_add x y))])))

    (def <> (fun maybe maybe maybe)
      (lambda [assoc] (x maybe) (y maybe)
        (cases (Pair x y)
          [(Pair Nothing y) y]
          [(Pair x Nothing) x]
          [(Pair (Just x) (Just y)) (Just (nat_add x y))])))
  """).get,

  "maybe_monad_leftid" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type maybe {Nothing (Just nat)})

    (def return (lambda (x nat) (Just x)))

    (def >>= (fun maybe (fun nat maybe) maybe)
      (lambda (x maybe) (f (fun nat maybe))
        (cases x
          [Nothing Nothing]
          [(Just x) (f x)])))
  """).get.withCustomProperty(
    parser.deserialize("(>>= (return x) f)").get,
    parser.deserialize("(f x)").get,
    Set(Symbol("f"), Symbol("x")),
    Symbol(">>=")),

  "maybe_monad_rightid" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type maybe {Nothing (Just nat)})

    (def return (lambda (x nat) (Just x)))

    (def >>= (fun maybe (fun nat maybe) maybe)
      (lambda (x maybe) (f (fun nat maybe))
        (cases x
          [Nothing Nothing]
          [(Just x) (f x)])))
  """).get.withCustomProperty(
    parser.deserialize("(>>= m return)").get,
    parser.deserialize("m").get,
    Set(Symbol("m")),
    Symbol(">>=")),

  "maybe_monad_assoc" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type maybe {Nothing (Just nat)})

    (def return (lambda (x nat) (Just x)))

    (def >>= (fun maybe (fun nat maybe) maybe)
      (lambda (x maybe) (f (fun nat maybe))
        (cases x
          [Nothing Nothing]
          [(Just x) (f x)])))
  """).get.withCustomProperty(
    parser.deserialize("(>>= (>>= m f) g)").get,
    parser.deserialize("(>>= m (lambda (x nat) (>>= (f x) g)))").get,
    Set(Symbol("m"), Symbol("f"), Symbol("g")),
    Symbol(">>=")),

  "list_functor_id" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type list {Nil (Cons nat list)})

    (def fmap (fun (fun nat nat) list list)
      (lambda (f (fun nat nat)) (x list)
        (cases x
          [Nil Nil]
          [(Cons x xs) (Cons (f x) (fmap f xs))])))
  """).get.withCustomProperty(
    parser.deserialize("(fmap (lambda (y nat) y) x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("fmap")),

  "list_functor_composition" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type list {Nil (Cons nat list)})

    (def fmap (fun (fun nat nat) list list)
      (lambda (f (fun nat nat)) (x list)
        (cases x
          [Nil Nil]
          [(Cons x xs) (Cons (f x) (fmap f xs))])))
  """).get.withCustomProperty(
    parser.deserialize("(fmap (lambda (y nat) (f (g y))) x)").get,
    parser.deserialize("(fmap f (fmap g x))").get,
    Set(Symbol("f"), Symbol("g"), Symbol("x")),
    Symbol("fmap")),

  "list_semigroup_assoc" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type list {Nil (Cons nat list)})

    (def <> (fun list list list)
      (lambda [assoc] (x list) (y list)
        (cases x
          [Nil y]
          [(Cons x xs) (Cons x (<> xs y))])))
  """).get,

  "list_monad_leftid" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type list {Nil (Cons nat list)})

    (def return (lambda (x nat) (Cons x Nil)))

    (def <> (fun list list list)
      (lambda (x list) (y list)
        (cases x
          [Nil y]
          [(Cons x xs) (Cons x (<> xs y))])))

    (def >>= (fun list (fun nat list) list)
      (lambda (x list) (f (fun nat list))
        (cases x
          [Nil Nil]
          [(Cons x xs) (<> (f x) (>>= xs f))])))
  """).get.withCustomProperty(
    parser.deserialize("(>>= (return x) f)").get,
    parser.deserialize("(f x)").get,
    Set(Symbol("f"), Symbol("x")),
    Symbol(">>=")),

  "list_monad_rightid" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type list {Nil (Cons nat list)})

    (def return (lambda (x nat) (Cons x Nil)))

    (def <> (fun list list list)
      (lambda (x list) (y list)
        (cases x
          [Nil y]
          [(Cons x xs) (Cons x (<> xs y))])))

    (def >>= (fun list (fun nat list) list)
      (lambda (x list) (f (fun nat list))
        (cases x
          [Nil Nil]
          [(Cons x xs) (<> (f x) (>>= xs f))])))
  """).get.withCustomProperty(
    parser.deserialize("(>>= m return)").get,
    parser.deserialize("m").get,
    Set(Symbol("m")),
    Symbol(">>=")),

  "list_monad_assoc" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type list {Nil (Cons nat list)})

    (def return (lambda (x nat) (Cons x Nil)))

    (def <> (fun list list list)
      (lambda (x list) (y list)
        (cases x
          [Nil y]
          [(Cons x xs) (Cons x (<> xs y))])))

    (def >>= (fun list (fun nat list) list)
      (lambda (x list) (f (fun nat list))
        (cases x
          [Nil Nil]
          [(Cons x xs) (<> (f x) (>>= xs f))])))
  """).get.withCustomProperty(
    parser.deserialize("(>>= (>>= m f) g)").get,
    parser.deserialize("(>>= m (lambda (x nat) (>>= (f x) g)))").get,
    Set(Symbol("m"), Symbol("f"), Symbol("g")),
    Symbol(">>=")),

  "function_functor_id" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type function (fun nat nat))

    (def fmap (fun (fun nat nat) function function)
      (lambda (f (fun nat nat)) (x function)
        (lambda (v nat) (f (x v)))))
  """).get.withCustomProperty(
    parser.deserialize("(fmap (lambda (y nat) y) x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("fmap")),

  "function_functor_composition" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type function (fun nat nat))

    (def fmap (fun (fun nat nat) function function)
      (lambda (f (fun nat nat)) (x function)
        (lambda (v nat) (f (x v)))))
  """).get.withCustomProperty(
    parser.deserialize("(fmap (lambda (y nat) (f (g y))) x)").get,
    parser.deserialize("(fmap f (fmap g x))").get,
    Set(Symbol("f"), Symbol("g"), Symbol("x")),
    Symbol("fmap")),

  "function_semigroup_assoc" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type function (fun nat nat))

    (def nat_add (fun nat nat nat)
      (lambda (x nat) (y nat) (cases x
        [Z y]
        [(S x) (S (nat_add x y))])))

    (def <> (fun function function function)
      (lambda [assoc] (x function) (y function)
        (lambda (v nat) (nat_add (x v) (y v)))))
  """).get,

  "function_monad_leftid" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type function (fun nat nat))

    (def return (lambda (x nat) (lambda (v nat) x)))

    (def >>= (fun function (fun nat function) function)
      (lambda (x function) (f (fun nat function))
        (lambda (v nat) (f (x v) v))))
  """).get.withCustomProperty(
    parser.deserialize("(>>= (return x) f)").get,
    parser.deserialize("(f x)").get,
    Set(Symbol("f"), Symbol("x")),
    Symbol(">>=")),

  "function_monad_rightid" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type function (fun nat nat))

    (def return (lambda (x nat) (lambda (v nat) x)))

    (def >>= (fun function (fun nat function) function)
      (lambda (x function) (f (fun nat function))
        (lambda (v nat) (f (x v) v))))
  """).get.withCustomProperty(
    parser.deserialize("(>>= m return)").get,
    parser.deserialize("m").get,
    Set(Symbol("m")),
    Symbol(">>=")),

  "function_monad_assoc" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type function (fun nat nat))

    (def return (lambda (x nat) (lambda (v nat) x)))

    (def >>= (fun function (fun nat function) function)
      (lambda (x function) (f (fun nat function))
        (lambda (v nat) (f (x v) v))))
  """).get.withCustomProperty(
    parser.deserialize("(>>= (>>= m f) g)").get,
    parser.deserialize("(>>= m (lambda (x nat) (>>= (f x) g)))").get,
    Set(Symbol("m"), Symbol("f"), Symbol("g")),
    Symbol(">>=")),

  "pair_functor_id" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type pair {(Pair nat nat)})

    (def fmap (fun (fun nat nat) pair pair)
      (lambda (f (fun nat nat)) (x pair)
        (let (Pair a b) x (Pair a (f b)))))
  """).get.withCustomProperty(
    parser.deserialize("(fmap (lambda (y nat) y) x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("fmap")),

  "pair_functor_composition" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type pair {(Pair nat nat)})

    (def fmap (fun (fun nat nat) pair pair)
      (lambda (f (fun nat nat)) (x pair)
        (let (Pair a b) x (Pair a (f b)))))
  """).get.withCustomProperty(
    parser.deserialize("(fmap (lambda (y nat) (f (g y))) x)").get,
    parser.deserialize("(fmap f (fmap g x))").get,
    Set(Symbol("f"), Symbol("g"), Symbol("x")),
    Symbol("fmap")),

  "pair_semigroup_assoc" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type pair {(Pair nat nat)})

    (def nat_add (fun nat nat nat)
      (lambda (x nat) (y nat) (cases x
        [Z y]
        [(S x) (S (nat_add x y))])))

    (def <> (fun pair pair pair)
      (lambda [assoc] (x pair) (y pair)
        (let (Pair (Pair xa xb) (Pair ya yb)) (Pair x y) (Pair (nat_add xa ya) (nat_add xb yb)))))
  """).get,

  "pair_monad_leftid" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type pair {(Pair nat nat)})

    (def return (lambda (x nat) (Pair Z x)))

    (def nat_add (fun nat nat nat)
      (lambda (x nat) (y nat) (cases x
        [Z y]
        [(S x) (S (nat_add x y))])))

    (def >>= (fun pair (fun nat pair) pair)
      (lambda (x pair) (f (fun nat pair))
        (let (Pair a b) x
          (let (Pair u v) (f b)
            (Pair (nat_add a u) v)))))
  """).get.withCustomProperty(
    parser.deserialize("(>>= (return x) f)").get,
    parser.deserialize("(f x)").get,
    Set(Symbol("f"), Symbol("x")),
    Symbol(">>=")),

  "pair_monad_rightid" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type pair {(Pair nat nat)})

    (def return (lambda (x nat) (Pair Z x)))

    (def nat_add (fun nat nat nat)
      (lambda (x nat) (y nat) (cases x
        [Z y]
        [(S x) (S (nat_add x y))])))

    (def >>= (fun pair (fun nat pair) pair)
      (lambda (x pair) (f (fun nat pair))
        (let (Pair a b) x
          (let (Pair u v) (f b)
            (Pair (nat_add a u) v)))))
  """).get.withCustomProperty(
    parser.deserialize("(>>= m return)").get,
    parser.deserialize("m").get,
    Set(Symbol("m")),
    Symbol(">>=")),

  "pair_monad_assoc" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type pair {(Pair nat nat)})

    (def return (lambda (x nat) (Pair Z x)))

    (def nat_add (fun nat nat nat)
      (lambda (x nat) (y nat) (cases x
        [Z y]
        [(S x) (S (nat_add x y))])))

    (def >>= (fun pair (fun nat pair) pair)
      (lambda (x pair) (f (fun nat pair))
        (let (Pair a b) x
          (let (Pair u v) (f b)
            (Pair (nat_add a u) v)))))
  """).get.withCustomProperty(
    parser.deserialize("(>>= (>>= m f) g)").get,
    parser.deserialize("(>>= m (lambda (x nat) (>>= (f x) g)))").get,
    Set(Symbol("m"), Symbol("f"), Symbol("g")),
    Symbol(">>=")),

  "state_functor_id" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type state (fun nat {(Return nat nat)}))

    (def fmap (fun (fun nat nat) state state)
      (lambda (f (fun nat nat)) (m state)
        (lambda (r nat)
          (let (Return x s) (m r) (Return (f x) s)))))
  """).get.withCustomProperty(
    parser.deserialize("(fmap (lambda (y nat) y) x)").get,
    parser.deserialize("x").get,
    Set(Symbol("x")),
    Symbol("fmap")),

  "state_functor_composition" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type state (fun nat {(Return nat nat)}))

    (def fmap (fun (fun nat nat) state state)
      (lambda (f (fun nat nat)) (m state)
        (lambda (r nat)
          (let (Return x s) (m r) (Return (f x) s)))))
  """).get.withCustomProperty(
    parser.deserialize("(fmap (lambda (y nat) (f (g y))) x)").get,
    parser.deserialize("(fmap f (fmap g x))").get,
    Set(Symbol("f"), Symbol("g"), Symbol("x")),
    Symbol("fmap")),

  "state_semigroup_assoc" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type state (fun nat {(Return nat nat)}))

    (def nat_add (fun nat nat nat)
      (lambda (x nat) (y nat) (cases x
        [Z y]
        [(S x) (S (nat_add x y))])))

    (def <> (fun state state state)
      (lambda [assoc] (m state) (n state)
        (lambda (r nat)
          (let (Return x t) (m r)
            (let (Return y s) (n t)
              (Return (nat_add x y) s))))))
  """).get,

  "state_monad_leftid" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type state (fun nat {(Return nat nat)}))

    (def return (lambda (x nat)
      (lambda (s nat) (Return x s))))

    (def >>= (fun state (fun nat state) state)
      (lambda (m state) (f (fun nat state))
        (lambda (r nat)
          (let (Return x s) (m r) ((f x) s)))))
  """).get.withCustomProperty(
    parser.deserialize("(>>= (return x) f)").get,
    parser.deserialize("(f x)").get,
    Set(Symbol("f"), Symbol("x")),
    Symbol(">>=")),

  "state_monad_rightid" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type state (fun nat {(Return nat nat)}))

    (def return (lambda (x nat)
      (lambda (s nat) (Return x s))))

    (def >>= (fun state (fun nat state) state)
      (lambda (m state) (f (fun nat state))
        (lambda (r nat)
          (let (Return x s) (m r) ((f x) s)))))
  """).get.withCustomProperty(
    parser.deserialize("(>>= m return)").get,
    parser.deserialize("m").get,
    Set(Symbol("m")),
    Symbol(">>=")),

  "state_monad_assoc" ->
  parser.deserialize("""
    (type nat {Z (S nat)})
    (type state (fun nat {(Return nat nat)}))

    (def return (lambda (x nat)
      (lambda (s nat) (Return x s))))

    (def >>= (fun state (fun nat state) state)
      (lambda (m state) (f (fun nat state))
        (lambda (r nat)
          (let (Return x s) (m r) ((f x) s)))))
  """).get.withCustomProperty(
    parser.deserialize("(>>= (>>= m f) g)").get,
    parser.deserialize("(>>= m (lambda (x nat) (>>= (f x) g)))").get,
    Set(Symbol("m"), Symbol("f"), Symbol("g")),
    Symbol(">>=")),

  "tip_bin_plus_assoc" ->
  parser.deserialize("""
    (letrec bin_s (fun (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}))
      (lambda (x (rec X {(ZeroAnd X) (OneAnd X) One})) (cases x
        [One (ZeroAnd One)]
        [(ZeroAnd xs) (OneAnd xs)]
        [(OneAnd ys) (ZeroAnd (bin_s ys))]))
      (letrec tip_bin_plus (fun (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}))
        (lambda [assoc] (x (rec X {(ZeroAnd X) (OneAnd X) One})) (y (rec X {(ZeroAnd X) (OneAnd X) One})) (cases x
          [One (bin_s y)]
          [(ZeroAnd z) (cases y
            [One (bin_s x)]
            [(ZeroAnd ys) (ZeroAnd (tip_bin_plus z ys))]
            [(OneAnd xs) (OneAnd (tip_bin_plus z xs))])]
          [(OneAnd x2) (cases y
            [One (bin_s x)]
            [(ZeroAnd zs) (OneAnd (tip_bin_plus x2 zs))]
            [(OneAnd ys2) (ZeroAnd (bin_s (tip_bin_plus x2 ys2)))])]))
        Unit))
  """).get,

  "tip_bin_plus_comm" ->
  parser.deserialize("""
    (letrec bin_s (fun (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}))
      (lambda (x (rec X {(ZeroAnd X) (OneAnd X) One})) (cases x
        [One (ZeroAnd One)]
        [(ZeroAnd xs) (OneAnd xs)]
        [(OneAnd ys) (ZeroAnd (bin_s ys))]))
      (letrec tip_bin_plus (fun (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}))
        (lambda [comm] (x (rec X {(ZeroAnd X) (OneAnd X) One})) (y (rec X {(ZeroAnd X) (OneAnd X) One})) (cases x
          [One (bin_s y)]
          [(ZeroAnd z) (cases y
            [One (bin_s x)]
            [(ZeroAnd ys) (ZeroAnd (tip_bin_plus z ys))]
            [(OneAnd xs) (OneAnd (tip_bin_plus z xs))])]
          [(OneAnd x2) (cases y
            [One (bin_s x)]
            [(ZeroAnd zs) (OneAnd (tip_bin_plus x2 zs))]
            [(OneAnd ys2) (ZeroAnd (bin_s (tip_bin_plus x2 ys2)))])]))
        Unit))
  """).get,

  "tip_bin_times_assoc" ->
  parser.deserialize("""
    (letrec bin_s (fun (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}))
      (lambda (x (rec X {(ZeroAnd X) (OneAnd X) One})) (cases x
        [One (ZeroAnd One)]
        [(ZeroAnd xs) (OneAnd xs)]
        [(OneAnd ys) (ZeroAnd (bin_s ys))]))
      (letrec tip_bin_plus (fun (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}))
        (lambda (x (rec X {(ZeroAnd X) (OneAnd X) One})) (y (rec X {(ZeroAnd X) (OneAnd X) One})) (cases x
          [One (bin_s y)]
          [(ZeroAnd z) (cases y
            [One (bin_s x)]
            [(ZeroAnd ys) (ZeroAnd (tip_bin_plus z ys))]
            [(OneAnd xs) (OneAnd (tip_bin_plus z xs))])]
          [(OneAnd x2) (cases y
            [One (bin_s x)]
            [(ZeroAnd zs) (OneAnd (tip_bin_plus x2 zs))]
            [(OneAnd ys2) (ZeroAnd (bin_s (tip_bin_plus x2 ys2)))])]))
        (letrec tip_bin_times (fun (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}))
          (lambda [assoc] (x (rec X {(ZeroAnd X) (OneAnd X) One})) (y (rec X {(ZeroAnd X) (OneAnd X) One})) (cases x
            [One y]
            [(ZeroAnd xs1) (ZeroAnd (tip_bin_times xs1 y))]
            [(OneAnd xs12) (tip_bin_plus (ZeroAnd (tip_bin_times xs12 y)) y)]))
          Unit)))
  """).get,

  "tip_bin_times_comm" ->
  parser.deserialize("""
    (letrec bin_s (fun (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}))
      (lambda (x (rec X {(ZeroAnd X) (OneAnd X) One})) (cases x
        [One (ZeroAnd One)]
        [(ZeroAnd xs) (OneAnd xs)]
        [(OneAnd ys) (ZeroAnd (bin_s ys))]))
      (letrec tip_bin_plus (fun (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}))
        (lambda (x (rec X {(ZeroAnd X) (OneAnd X) One})) (y (rec X {(ZeroAnd X) (OneAnd X) One})) (cases x
          [One (bin_s y)]
          [(ZeroAnd z) (cases y
            [One (bin_s x)]
            [(ZeroAnd ys) (ZeroAnd (tip_bin_plus z ys))]
            [(OneAnd xs) (OneAnd (tip_bin_plus z xs))])]
          [(OneAnd x2) (cases y
            [One (bin_s x)]
            [(ZeroAnd zs) (OneAnd (tip_bin_plus x2 zs))]
            [(OneAnd ys2) (ZeroAnd (bin_s (tip_bin_plus x2 ys2)))])]))
        (letrec tip_bin_times (fun (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}) (rec X {(ZeroAnd X) (OneAnd X) One}))
          (lambda [comm] (x (rec X {(ZeroAnd X) (OneAnd X) One})) (y (rec X {(ZeroAnd X) (OneAnd X) One})) (cases x
            [One y]
            [(ZeroAnd xs1) (ZeroAnd (tip_bin_times xs1 y))]
            [(OneAnd xs12) (tip_bin_plus (ZeroAnd (tip_bin_times xs12 y)) y)]))
          Unit)))
  """).get,

  "tip_int_plus_assoc" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      (letrec tip_sub (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))})
        (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (let fail
            (cases y
              [Z (P x)]
              [(S z) (cases x
                [Z (N z)]
                [(S x2) (tip_sub x2 z)])])
            (cases x
              [Z (cases y
                [Z (P Z)]
                [(S x3) fail])]
              [(S x4) fail])))
        (let tip_int_plus
          (lambda [assoc] (x {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))}) (y {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))}) (cases x
            [(P m) (cases y
              [(P n) (P (tip_nat_plus m n))]
              [(N o) (tip_sub m (tip_nat_plus (S Z) o))])]
            [(N m2) (cases y
              [(P n2) (tip_sub n2 (tip_nat_plus (S Z) m2))]
              [(N n3) (N (tip_nat_plus (tip_nat_plus (S Z) m2) n3))])]))
          Unit)))
  """).get,

  "tip_int_plus_comm" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      (letrec tip_sub (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))})
        (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (let fail
            (cases y
              [Z (P x)]
              [(S z) (cases x
                [Z (N z)]
                [(S x2) (tip_sub x2 z)])])
            (cases x
              [Z (cases y
                [Z (P Z)]
                [(S x3) fail])]
              [(S x4) fail])))
        (let tip_int_plus
          (lambda [comm] (x {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))}) (y {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))}) (cases x
            [(P m) (cases y
              [(P n) (P (tip_nat_plus m n))]
              [(N o) (tip_sub m (tip_nat_plus (S Z) o))])]
            [(N m2) (cases y
              [(P n2) (tip_sub n2 (tip_nat_plus (S Z) m2))]
              [(N n3) (N (tip_nat_plus (tip_nat_plus (S Z) m2) n3))])]))
          Unit)))
  """).get,

  "tip_int_times_assoc" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      (letrec tip_nat_times (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S z) (tip_nat_plus y (tip_nat_times z y))]))
       (let tip_to_integer
         (lambda (x {Pos Neg}) (y (rec X {(S X) Z})) (cases x
           [Pos (P y)]
           [Neg (cases y
             [Z (P Z)]
             [(S z) (N z)])]))
         (let tip_sign
           (lambda (x {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))}) (cases x
             [(P y) Pos]
             [(N z) Neg]))
           (let tip_opposite_sign
             (lambda (x {Pos Neg}) (cases x
               [Pos Neg]
               [Neg Pos]))
             (let tip_times_sign
               (lambda (x {Pos Neg}) (y {Pos Neg}) (cases x
                 [Pos y]
                 [Neg (tip_opposite_sign y)]))
               (let tip_abs
                 (lambda (x {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))}) (cases x
                   [(P n) n]
                   [(N m) (tip_nat_plus (S Z) m)]))
                (let tip_int_times
                  (lambda [assoc] (x {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))}) (y {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))})
                    (tip_to_integer
                      (tip_times_sign (tip_sign x) (tip_sign y))
                      (tip_nat_times (tip_abs x) (tip_abs y))))
                  Unit))))))))
  """).get,

  "tip_int_times_comm" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      (letrec tip_nat_times (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S z) (tip_nat_plus y (tip_nat_times z y))]))
       (let tip_to_integer
         (lambda (x {Pos Neg}) (y (rec X {(S X) Z})) (cases x
           [Pos (P y)]
           [Neg (cases y
             [Z (P Z)]
             [(S z) (N z)])]))
         (let tip_sign
           (lambda (x {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))}) (cases x
             [(P y) Pos]
             [(N z) Neg]))
           (let tip_opposite_sign
             (lambda (x {Pos Neg}) (cases x
               [Pos Neg]
               [Neg Pos]))
             (let tip_times_sign
               (lambda (x {Pos Neg}) (y {Pos Neg}) (cases x
                 [Pos y]
                 [Neg (tip_opposite_sign y)]))
               (let tip_abs
                 (lambda (x {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))}) (cases x
                   [(P n) n]
                   [(N m) (tip_nat_plus (S Z) m)]))
                (let tip_int_times
                  (lambda [comm] (x {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))}) (y {(P (rec X {(S X) Z})) (N (rec X {(S X) Z}))})
                    (tip_to_integer
                      (tip_times_sign (tip_sign x) (tip_sign y))
                      (tip_nat_times (tip_abs x) (tip_abs y))))
                  Unit))))))))
  """).get,

  "tip_list_append_assoc" ->
  parser.deserialize("""
    (letrec tip_list_append (forall T (fun (rec X {(Cons T X) Nil}) (rec X {(Cons T X) Nil}) (rec X {(Cons T X) Nil})))
      (lambda T (lambda [assoc] (x (rec X {(Cons T X) Nil})) (y (rec X {(Cons T X) Nil})) (cases x
        [Nil y]
        [(Cons z xs) (Cons z ((tip_list_append [T]) xs y))])))
      Unit)
  """).get,

  "tip_nat_geq_antisym" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      (let tip_nat_geq
        (lambda [antisym] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (tip_nat_leq y x))
        Unit))
  """).get,

  "tip_nat_geq_refl" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      (let tip_nat_geq
        (lambda [refl] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (tip_nat_leq y x))
        Unit))
  """).get,

  "tip_nat_geq_trans" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      (let tip_nat_geq
        (lambda [trans] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (tip_nat_leq y x))
        Unit))
  """).get,

  "tip_nat_gt_asym" ->
  parser.deserialize("""
    (letrec tip_nat_lt (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases y
        [Z False]
        [(S z) (cases x
          [Z True]
          [(S n) (tip_nat_lt n z)])]))
      (let tip_nat_gt
        (lambda [asym] (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (tip_nat_lt y x))
        Unit))
  """).get,

  "tip_nat_gt_irefl" ->
  parser.deserialize("""
    (letrec tip_nat_lt (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases y
        [Z False]
        [(S z) (cases x
          [Z True]
          [(S n) (tip_nat_lt n z)])]))
      (let tip_nat_gt
        (lambda [irefl] (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (tip_nat_lt y x))
        Unit))
  """).get,

  "tip_nat_gt_trans" ->
  parser.deserialize("""
    (letrec tip_nat_lt (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases y
        [Z False]
        [(S z) (cases x
          [Z True]
          [(S n) (tip_nat_lt n z)])]))
      (let tip_nat_gt
        (lambda [trans] (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (tip_nat_lt y x))
        Unit))
  """).get,

  "tip_nat_leq_antisym" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda [antisym] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      Unit)
  """).get,

  "tip_nat_leq_refl" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda [refl] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      Unit)
  """).get,

  "tip_nat_leq_trans" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda [trans] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      Unit)
  """).get,

  "tip_nat_lt_asym" ->
  parser.deserialize("""
    (letrec tip_nat_lt (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda [asym] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases y
        [Z False]
        [(S z) (cases x
          [Z True]
          [(S n) (tip_nat_lt n z)])]))
        Unit)
  """).get,

  "tip_nat_lt_irefl" ->
  parser.deserialize("""
    (letrec tip_nat_lt (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda [irefl] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases y
        [Z False]
        [(S z) (cases x
          [Z True]
          [(S n) (tip_nat_lt n z)])]))
        Unit)
  """).get,

  "tip_nat_lt_trans" ->
  parser.deserialize("""
    (letrec tip_nat_lt (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda [trans] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases y
        [Z False]
        [(S z) (cases x
          [Z True]
          [(S n) (tip_nat_lt n z)])]))
        Unit)
  """).get,

  "tip_nat_max_assoc" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      (let tip_nat_max
        (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (if (tip_nat_leq x y) y x))
        Unit))
  """).get,

  "tip_nat_max_comm" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      (let tip_nat_max
        (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (if (tip_nat_leq x y) y x))
        Unit))
  """).get,

  "tip_nat_max_idem" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      (let tip_nat_max
        (lambda [idem] (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (if (tip_nat_leq x y) y x))
        Unit))
  """).get,

  "tip_nat_min_assoc" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      (let tip_nat_min
        (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (if (tip_nat_leq x y) x y))
        Unit))
  """).get,

  "tip_nat_min_comm" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      (let tip_nat_min
        (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (if (tip_nat_leq x y) x y))
        Unit))
  """).get,

  "tip_nat_min_idem" ->
  parser.deserialize("""
    (letrec tip_nat_leq (fun (rec X {(S X) Z}) (rec X {(S X) Z}) {True False})
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z True]
        [(S z) (cases y
          [Z False]
          [(S x2) (tip_nat_leq z x2)])]))
      (let tip_nat_min
        (lambda [idem] (x (rec X {(S X) Z})) (y (rec X {(S X) Z}))
          (if (tip_nat_leq x y) x y))
        Unit))
  """).get,

  "tip_nat_plus_acc_assoc" ->
  parser.deserialize("""
    (letrec tip_nat_plus_acc (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (tip_nat_plus_acc z (S y))]))
      Unit)
  """).get,

  "tip_nat_plus_acc_comm" ->
  parser.deserialize("""
    (letrec tip_nat_plus_acc (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (tip_nat_plus_acc z (S y))]))
      Unit)
  """).get,

  "tip_nat_plus_assoc" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      Unit)
  """).get,

  "tip_nat_plus_comm" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      Unit)
  """).get,

  "tip_nat_times_acc_assoc" ->
  parser.deserialize("""
    (letrec tip_nat_plus_acc (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (tip_nat_plus_acc z (S y))]))
      (letrec tip_nat_times_acc (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S z) (cases y
            [Z Z]
            [(S x2) (tip_nat_plus_acc x (tip_nat_plus_acc x2 (tip_nat_times_acc z x2)))])]))
        Unit))
  """).get,

  "tip_nat_times_acc_comm" ->
  parser.deserialize("""
    (letrec tip_nat_plus_acc (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (tip_nat_plus_acc z (S y))]))
      (letrec tip_nat_times_acc (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S z) (cases y
            [Z Z]
            [(S x2) (tip_nat_plus_acc x (tip_nat_plus_acc x2 (tip_nat_times_acc z x2)))])]))
        Unit))
  """).get,

  "tip_nat_times_alt_assoc" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      (letrec tip_nat_times_alt (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S z) (cases y
            [Z Z]
            [(S x2) (tip_nat_plus (tip_nat_plus (tip_nat_plus (S Z) (tip_nat_times_alt z x2)) z) x2)])]))
        Unit))
  """).get,

  "tip_nat_times_alt_comm" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      (letrec tip_nat_times_alt (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S z) (cases y
            [Z Z]
            [(S x2) (tip_nat_plus (tip_nat_plus (tip_nat_plus (S Z) (tip_nat_times_alt z x2)) z) x2)])]))
        Unit))
  """).get,

  "tip_nat_times_assoc" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      (letrec tip_nat_times (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S z) (tip_nat_plus y (tip_nat_times z y))]))
        Unit))
  """).get,

  "tip_nat_times_comm" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      (letrec tip_nat_times (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
          [Z Z]
          [(S z) (tip_nat_plus y (tip_nat_times z y))]))
        Unit))
  """).get,

  "tip_nat_times_weird_assoc" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      (letrec tip_add3acc (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (z (rec X {(S X) Z})) (cases x
          [Z (cases y
            [Z z]
            [(S x2) (tip_add3acc Z x2 (S z))])]
          [(S x3) (tip_add3acc x3 (S y) z)]))
        (letrec nat_times_weird (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
          (lambda [assoc] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
            [Z Z]
            [(S z) (cases y
              [Z Z]
              [(S x2) (tip_nat_plus (S Z) (tip_add3acc z x2 (nat_times_weird z x2)))])]))
          Unit)))
  """).get,

  "tip_nat_times_weird_comm" ->
  parser.deserialize("""
    (letrec tip_nat_plus (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
      (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
        [Z y]
        [(S z) (S (tip_nat_plus z y))]))
      (letrec tip_add3acc (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
        (lambda (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (z (rec X {(S X) Z})) (cases x
          [Z (cases y
            [Z z]
            [(S x2) (tip_add3acc Z x2 (S z))])]
          [(S x3) (tip_add3acc x3 (S y) z)]))
        (letrec nat_times_weird (fun (rec X {(S X) Z}) (rec X {(S X) Z}) (rec X {(S X) Z}))
          (lambda [comm] (x (rec X {(S X) Z})) (y (rec X {(S X) Z})) (cases x
            [Z Z]
            [(S z) (cases y
              [Z Z]
              [(S x2) (tip_nat_plus (S Z) (tip_add3acc z x2 (nat_times_weird z x2)))])]))
          Unit)))
  """).get,
)
