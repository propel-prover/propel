package propel
package parser

import scala.annotation.switch
import scala.util.{Failure, Success, Try}

enum Bracket:
  case Paren
  case Square
  case Brace

enum Quote:
  case None
  case Single
  case Double

enum SExpr:
  case Atom(identifier: String, quote: Quote)
  case Expr(expressions: List[SExpr], bracket: Bracket)

object SExpr:
  private inline def special(ch: Char) = (ch: @switch) match
    case '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';' => true
    case _ => Character.isWhitespace(ch) || Character.isSpaceChar(ch)

  def requiresQuotes(identifier: String) =
    val length = identifier.length
    var requiresQuotes = false
    var i = 0
    while !requiresQuotes && i < length do
      (identifier(i): @switch) match
        case '\b' | '\t' | '\n' | '\f' | '\r' | '\"' | '\'' | '\\' => requiresQuotes = true
        case _ => if special(identifier(i)) then requiresQuotes = true
      i += 1
    requiresQuotes

  def deserialize(string: String): Try[List[SExpr]] =
    val length = string.length
    var i = 0

    inline def hasNext =
      i < length
    inline def next() =
      val j = i
      i += 1
      string(j)
    inline def peak() =
      string(i)

    def excerpt =
      inline val length = 20
      if i <= length then string.substring(0, i)
      else s"... ${string.substring(i - length, i)}"

    val builder = StringBuilder()

    def deserializeIdentifier(starting: Char): String =
      var closed = false
      var escaped = false

      builder.clear()
      
      if starting != '\"' && starting != '\'' then
        builder += starting

      while !closed && hasNext do
        val ch = peak()
        if escaped then
          next()
          escaped = false
          (ch: @switch) match
            case 'b' => builder += '\b'
            case 't' => builder += '\t'
            case 'n' => builder += '\n'
            case 'f' => builder += '\f'
            case 'r' => builder += '\r'
            case '\"' => builder += '\"'
            case '\'' => builder += '\''
            case '\\' => builder += '\\'
            case _ => throw ParserException(s"Invalid escape sequence: $excerpt")
        else if ch == '\"' || ch == '\'' then
          next()
          if starting == ch then
            if hasNext then
              val ch = peak()
              if !special(ch) then
                next()
                throw ParserException(s"Unexpected $ch: $excerpt")
            closed = true
          else if starting != '\"' && starting != '\'' then
            throw ParserException(s"Unmatched $ch: $excerpt")
          else
            builder += ch
        else if starting != '\"' && starting != '\'' then
          if special(ch) then
            closed = true
          else
            next()
            builder += ch
        else
          next()
          if ch == '\\' then escaped = true else builder += ch
      end while

      if (starting == '\"' || starting == '\'') && !closed then
        throw ParserException(s"Unclosed string: $excerpt")

      builder.result()
    end deserializeIdentifier

    def deserializeExpressions(closing: Char): List[SExpr] =
      var closed = false
      var expressions = List.empty[SExpr]

      while !closed && hasNext do
        (next(): @switch) match
          case '(' => expressions ::= Expr(deserializeExpressions(')'), Bracket.Paren)
          case '[' => expressions ::= Expr(deserializeExpressions(']'), Bracket.Square)
          case '{' => expressions ::= Expr(deserializeExpressions('}'), Bracket.Brace)

          case ')' =>
            if closing != ')' then throw ParserException(s"Unmatched (...): $excerpt")
            closed = true
          case ']' =>
            if closing != ']' then throw ParserException(s"Unmatched [...]: $excerpt")
            closed = true
          case '}' =>
            if closing != '}' then throw ParserException(s"Unmatched {...}: $excerpt")
            closed = true

          case '\"' => expressions ::= Atom(deserializeIdentifier('\"'), Quote.Double)
          case '\'' => expressions ::= Atom(deserializeIdentifier('\''), Quote.Single)
          case ch => if !special(ch) then expressions ::= Atom(deserializeIdentifier(ch), Quote.None)
      end while

      if !closed then
        (closing: @switch) match
          case ')' => throw ParserException(s"Unclosed (...): $excerpt")
          case ']' => throw ParserException(s"Unclosed [...]: $excerpt")
          case '}' => throw ParserException(s"Unclosed {...}: $excerpt")
          case _ =>

      expressions.reverse
    end deserializeExpressions

    try Success(deserializeExpressions(' '))
    catch case e: ParserException => Failure(e)
  end deserialize

  def serialize(expr: SExpr): String =
    val builder = StringBuilder()

    def serialize(expr: SExpr): Unit = expr match
      case Atom(identifier, quote) =>
        val length = identifier.length
        val ch =
          if quote == Quote.None then
            var i = 0
            var ch = ' '
            while ch == ' ' && i < length do
              (identifier(i): @switch) match
                case '\b' | '\t' | '\n' | '\f' | '\r' | '\"' | '\'' | '\\' => ch = '\"'
                case _ => if special(identifier(i)) then ch = '\"'
              i += 1
            ch
          else if quote == Quote.Single then
            '\''
          else
            '\"'

        if ch != ' ' then builder += ch

        var i = 0
        while i < length do
          (identifier(i): @switch) match
            case '\b' => builder ++= "\\b"
            case '\t' => builder ++= "\\t"
            case '\n' => builder ++= "\\n"
            case '\f' => builder ++= "\\f"
            case '\r' => builder ++= "\\r"
            case '\"' => builder ++= "\\\""
            case '\'' => builder ++= "\\\'"
            case '\\' => builder ++= "\\\\"
            case ch => builder += ch
          i += 1

        if ch != ' ' then builder += ch

      case Expr(expressions: List[SExpr], bracket: Bracket) =>
        (bracket: @switch) match
          case Bracket.Paren => builder += '('
          case Bracket.Square => builder += '['
          case Bracket.Brace => builder += '{'

        var rest = expressions
        while rest.nonEmpty do
          serialize(rest.head)
          rest = rest.tail
          if rest.nonEmpty then builder += ' '

        (bracket: @switch) match
          case Bracket.Paren => builder += ')'
          case Bracket.Square => builder += ']'
          case Bracket.Brace => builder += '}'
    end serialize

    serialize(expr)
    builder.result()
  end serialize
end SExpr
