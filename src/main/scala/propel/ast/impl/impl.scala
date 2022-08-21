package propel
package ast
package impl

import scala.quoted.*
import scala.runtime.Tuples


inline def defaultHashCode: Int = ${ defaultHashCodeImpl }

def defaultHashCodeImpl(using Quotes) =
  import quotes.reflect.*

  def classSymbol(symbol: Symbol): Symbol =
    if symbol.exists && !symbol.isClassDef then classSymbol(symbol.owner) else symbol
  
  val murmurHash3 = TypeRepr.of[scala.util.hashing.MurmurHash3.type].termSymbol
  val productHash = murmurHash3.declaredMethod("productHash").head

  Ref(productHash).appliedTo(This(classSymbol(Symbol.spliceOwner))).asExprOf[Int]
end defaultHashCodeImpl


inline def defaultApply[T]: T = ${ defaultApplyImpl[T] }

def defaultApplyImpl[T: Type](using Quotes) =
  import quotes.reflect.*
  
  def applySymbol(symbol: Symbol): Symbol =
    if symbol.exists && symbol.name != "apply" then applySymbol(symbol.owner) else symbol

  val apply = applySymbol(Symbol.spliceOwner)
  val module = apply.owner
  val classSymbol = module.companionClass
  val classTree = TypeIdent(classSymbol)

  (apply.paramSymss: @unchecked) match
    case List(args) =>
      New(classTree)
        .select(classSymbol.primaryConstructor)
        .appliedToArgs(args map { Ref(_) })
        .appliedTo('{ Nil }.asTerm).asExprOf[T]

    case List(List(template), args) =>
      val seq = TypeRepr.of[Seq[?]]
      val enrichments = TypeRepr.of[Enrichable[?]].typeSymbol.methodMember("enrichments").head
      val eqSeq = Ref(Symbol.requiredMethod("propel.ast.impl.eqSeq"))
      val filter = Ref(Symbol.requiredMethod("propel.ast.Enrichments.filter"))
      val isInstanceOf = defn.AnyClass.methodMember("isInstanceOf").head
      val asInstanceOf = defn.AnyClass.methodMember("asInstanceOf").head
      val eq = defn.AnyRefClass.methodMember("eq").head
      val && = defn.BooleanClass.methodMember("&&").head
      val templateTree = Ref(template)

      val constructWithArgs = New(classTree).select(classSymbol.primaryConstructor).appliedToArgs(args map { Ref(_) })

      Block(
        List(
          If(
            templateTree.select(isInstanceOf).appliedToType(classTree.tpe),
            ValDef.let(Symbol.spliceOwner, "other", templateTree.select(asInstanceOf).appliedToType(classTree.tpe)) { other =>
              val cond = args map { arg =>
                val argTree = Ref(arg)
                if argTree.tpe <:< seq then
                  eqSeq.appliedTo(other.select(other.symbol.fieldMember(arg.name)), argTree)
                else
                  other.select(other.symbol.fieldMember(arg.name)).select(eq).appliedTo(argTree)
              } reduceLeft { _.select(&&).appliedTo(_) }

              If(
                cond,
                Return(other, apply),
                constructWithArgs.appliedTo(filter.appliedTo(other, other.select(enrichments))))
            },
            Literal(UnitConstant()))),
        ValDef.let(Symbol.spliceOwner, "dummy", constructWithArgs.appliedTo('{ Nil }.asTerm)) { dummy =>
          constructWithArgs.appliedTo(filter.appliedTo(dummy, templateTree.select(enrichments)))
        }).asExprOf[T]
end defaultApplyImpl


def eqSeq(l0: Seq[?], l1: Seq[?]): Boolean =
  (l0 eq l1) ||
  (l0.lengthCompare(l1) == 0) && eqIteratorOfSameLength(l0.iterator, l1.iterator)

def eqProduct(p0: Product, p1: Product): Boolean =
  ((p0, p1) match { case (p0: AnyRef, p1: AnyRef) => p0 eq p1 case _ => false }) ||
  (p0.getClass == p1.getClass) && eqIteratorOfSameLength(p0.productIterator, p1.productIterator)

def eqIteratorOfSameLength(i0: Iterator[?], i1: Iterator[?]): Boolean =
  i0 zip i1 forall {
    case (e0: Seq[?], e1: Seq[?]) => eqSeq(e0, e1)
    case (e0: Product, e1: Product) if Tuples.isInstanceOfTuple(e0) && Tuples.isInstanceOfTuple(e1) => eqProduct(e0, e1)
    case (e0: AnyRef, e1: AnyRef) => e0 eq e1
    case (e0, e1) => e0 == e1
  }
