package propel

import scala.io.Source
import scala.util.Using
import java.io.IOException
import scala.scalajs.js.annotation._


@main def check(arguments: String*) =
  def parsedArguments =
    import ast.Property.*

    var error = Option.empty[String]
    var content = Option.empty[String]
    var deduction = false
    var reduction = false
    var discoverAlgebraicProperties = true
    var disableEqualities = false
    var disableInequalities = false
    var ignorePosContradiction = false
    var ignoreNegContradiction = false
    var ignorePosNegContradiction = false
    var ignoreCyclicContradiction = false
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
     ignorePosNegContradiction, ignoreCyclicContradiction,
     keepRewritesBits, propertiesOrder)

  parsedArguments match
    case (Some(error), _, _, _, _, _, _, _, _, _, _, _, _) =>
      println(s"Error: $error")

    case (_, None, _, _, _, _, _, _, _, _, _, _, _) =>
      println("Usage: propel [ARGUMENT]...")
      println("Verifies the algebraic and relational properties of functions specified in Propel's input format.")
      println()
      println("Specifying one of the following arguments is required.")
      println("  -c CONTENT, --content CONTENT    use the input specified on the command line")
      println("  -f FILE, --file FILE             read the input from the specified file")
      println("  -i, --stdin                      read the input from standard input")
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
          ignorePosNegContradiction, ignoreCyclicContradiction,
          keepRewritesBits, propertiesOrder) =>
      parseAndCheckSourceCode(
        content, deduction, reduction, discoverAlgebraicProperties,
        disableEqualities, disableInequalities,
        ignorePosContradiction, ignoreNegContradiction,
        ignorePosNegContradiction, ignoreCyclicContradiction,
        keepRewritesBits, propertiesOrder)

@JSExportTopLevel("parseAndCheckSourceCode")
def parseAndCheckSourceCode(
    code: String,
    deduction: Boolean, reduction: Boolean, discoverAlgebraicProperties: Boolean,
    disableEqualities: Boolean, disableInequalities: Boolean,
    ignorePosContradiction: Boolean, ignoreNegContradiction: Boolean,
    ignorePosNegContradiction: Boolean, ignoreCyclicContradiction: Boolean,
    keepRewritesBits: Int, propertiesOrder: List[ast.Property]) =
  parser.deserialize(code).fold(
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
