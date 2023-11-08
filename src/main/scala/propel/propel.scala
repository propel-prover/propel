package propel

import scala.io.Source
import scala.util.{Success, Using, Failure}
import java.io.IOException
import scala.scalajs.js.annotation._


@main def check(arguments: String*) =
  def parsedArguments =
    import ast.Property.*

    var error = Option.empty[String]
    var content = Option.empty[String | ast.Term]
    var deduction = false
    var reduction = false
    var discoverAlgebraicProperties = true
    var disableEqualities = false
    var disableInequalities = false
    var ignorePosContradiction = false
    var ignoreNegContradiction = false
    var ignorePosNegContradiction = false
    var ignoreCyclicContradiction = false
    var runMain = false
    var keepRewritesBits = 8
    var propertiesOrder = List(
      Reflexive, Irreflexive, Antisymmetric, Symmetric, Connected, Transitive,
      Commutative, Selection, Idempotent, Associative)

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
          case arg =>
            error = Some(s"Unknown option: $arg")

    (error, content, deduction, reduction, discoverAlgebraicProperties,
     disableEqualities, disableInequalities,
     ignorePosContradiction, ignoreNegContradiction,
     ignorePosNegContradiction, ignoreCyclicContradiction, runMain,
     keepRewritesBits, propertiesOrder)

  parsedArguments match
    case (Some(error), _, _, _, _, _, _, _, _, _, _, _, _, _) =>
      println(s"Error: $error")

    case (_, None, _, _, _, _, _, _, _, _, _, _, _, _) =>
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
      println("      --keep-rewrites NUMBER       number of top-scored rewrites to keep")
      println("      --prop-order PROPERTIES      comma-separated list of properties")

    case (_, Some(content), deduction, reduction, discoverAlgebraicProperties,
          disableEqualities, disableInequalities,
          ignorePosContradiction, ignoreNegContradiction,
          ignorePosNegContradiction, ignoreCyclicContradiction, runMain,
          keepRewritesBits, propertiesOrder) =>
      parseAndCheckSourceCode(
        content, deduction, reduction, discoverAlgebraicProperties,
        disableEqualities, disableInequalities,
        ignorePosContradiction, ignoreNegContradiction,
        ignorePosNegContradiction, ignoreCyclicContradiction, runMain,
        keepRewritesBits, propertiesOrder)

@JSExportTopLevel("parseAndCheckSourceCode")
def parseAndCheckSourceCode(
    code: String | ast.Term,
    deduction: Boolean, reduction: Boolean, discoverAlgebraicProperties: Boolean,
    disableEqualities: Boolean, disableInequalities: Boolean,
    ignorePosContradiction: Boolean, ignoreNegContradiction: Boolean,
    ignorePosNegContradiction: Boolean, ignoreCyclicContradiction: Boolean,
    runMain: Boolean, keepRewritesBits: Int, propertiesOrder: List[ast.Property]) =
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
          printReductionDebugInfo = reduction)

        if deduction || reduction then
          println()

        val errors = printing.showErrors(term)
        if errors.isEmpty then
          println("✔ Check successful.")
        else
          println(errors)
          println("✘ Check failed.")
  )

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
        (lambda [comm] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
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
        (lambda [comm] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
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
        (lambda [comm] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
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
        (lambda [comm] (x (rec X {(B0 X) (B1 X) BZ})) (y (rec X {(B0 X) (B1 X) BZ})) (cases (Tuple x y)
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
)
