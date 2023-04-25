package propel

import scala.io.Source
import scala.util.Using
import java.io.IOException
import scala.scalajs.js.annotation._


@main def check(arguments: String*) =
  def parsedArguments =
    var error = Option.empty[String]
    var content = Option.empty[String]
    var deduction = false
    var reduction = false

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
          case arg =>
            error = Some(s"Unknown option: $arg")

    (error, content, deduction, reduction)

  parsedArguments match
    case (Some(error), _, _, _) =>
      println(s"Error: $error")

    case (_, None, _, _) =>
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

    case (_, Some(content), deduction, reduction) => parseAndCheckSourceCode(content, deduction, reduction)

@JSExportTopLevel("parseAndCheckSourceCode")
def parseAndCheckSourceCode(code: String, deduction: Boolean, reduction: Boolean) =
  parser.deserialize(code).fold(
    exception =>
      println(s"Error: ${exception.getMessage}"),

    expr =>
      val term = evaluator.properties.check(expr, printDeductionDebugInfo = deduction, printReductionDebugInfo = reduction)

      if deduction || reduction then
        println()

      val errors = printing.showErrors(term)
      if errors.isEmpty then
        println("✔ Check successful.")
      else
        println(errors)
        println("✘ Check failed.")
  )
