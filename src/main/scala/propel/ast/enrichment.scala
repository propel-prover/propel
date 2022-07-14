package propel
package ast

import util.*

transparent trait Enrichable[Enriched <: Enrichable[Enriched]]:
  this: Enriched =>

  import Enrichments.Enrichment.*

  def enrichments: Enrichments

  def info[E](enrichment: Enrichment[E]): Option[E] =
    enrichments.iterator map { _.enrichment } collectFirst enrichment.asInstance

  def withoutInfo(enrichment: Enrichment[?]): Enriched =
    val asInstance = enrichment.asInstance
    var removed = false
    val filtered = enrichments filterNot { instance =>
      val isInstance = asInstance isDefinedAt instance.enrichment
      if isInstance then removed = true
      isInstance
    }
    if removed then withEnrichment(this, filtered) else this

  def withInfo[E](enrichment: Enrichment.Intrinsic[Enriched, E]): (Enriched, E) =
    info(enrichment) match
      case Some(enrichment) =>
        this -> enrichment
      case _ =>
        let(enrichment.make(this)) { (enriched, enrichment) =>
          withEnrichment(enriched, Intrinsic(enrichment) :: enrichments) -> enrichment
        }

  def withInfo[E](enrichment: Enrichment.Extrinsic[Enriched, E])(make: => E): (Enriched, E) =
    info(enrichment) match
      case Some(enrichment) =>
        this -> enrichment
      case _ =>
        let(make) { enrichment =>
          withEnrichment(this, Extrinsic(enrichment) :: enrichments) -> enrichment
        }

  def withThisInfo[E](enrichment: Enrichment.Extrinsic[Enriched, E])(make: => E): Enriched =
    withoutInfo(enrichment).withInfo(enrichment)(make)._1

  protected def withEnrichment(enriched: Enriched, enrichments: Enrichments): Enriched


sealed trait Enrichment[E]:
  val asInstance: PartialFunction[Any, E]

object Enrichment:
  trait Extrinsic[Enriched <: Enrichable[Enriched], E] extends Enrichment[E]

  trait Intrinsic[Enriched <: Enrichable[Enriched], E] extends Enrichment[E]:
    def make(enriched: Enriched): (Enriched, E)

    extension [Enriched <: Enrichable[Enriched]](exprs: List[Enrichable[Enriched]])
      def info[E](enrichment: Enrichment[E]): List[Option[E]] =
        exprs map { _.info(enrichment) }
      def withoutInfo(enrichment: Enrichment[?]): List[Enriched] =
        exprs map { _.withoutInfo(enrichment) }
      def withInfo[E](enrichment: Intrinsic[Enriched, E]): (List[Enriched], List[E]) =
        (exprs map { _.withInfo(enrichment) }).unzip
      def withInfo[E](enrichment: Extrinsic[Enriched, E])(make: => E): (List[Enriched], List[E]) =
        (exprs map { _.withInfo(enrichment)(make) }).unzip
      def withThisInfo[E](enrichment: Extrinsic[Enriched, E])(make: => E): List[Enriched] =
        exprs map { _.withThisInfo(enrichment)(make) }


type Enrichments = List[Enrichments.Enrichment]

object Enrichments:
  enum Enrichment:
    def enrichment: Any
    case Extrinsic(enrichment: Any)
    case Intrinsic(enrichment: Any)

  def filter(enrichments: Enrichments) =
    enrichments collect { case enrichment: Enrichment.Extrinsic => enrichment }
