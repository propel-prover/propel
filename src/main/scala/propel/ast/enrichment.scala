package propel
package ast

import util.*
import scala.reflect.Typeable

transparent trait Enrichable[+Enriched <: Enrichable[Enriched]]:
  def enrichments: Enrichments

  protected def withEnrichments(enrichments: Enrichments): Enriched

object Enrichable:
  type Any = Enrichable[?]

  extension [Enriched <: Enrichable[Enriched]](self: Enriched)
    def info[E](enrichment: Enrichment.Base[?, E]): Option[E] =
      self.enrichments.iterator `collectFirstDefined` enrichment.asEnrichment

    def withInfo(enriched: Enrichable.Any): Enriched =
      let(Enrichments.filter(self, enriched.enrichments)) { enrichments =>
        if enrichments.nonEmpty then
          val filtered = self.enrichments filterNot { instance =>
            enrichments exists { _.enrichment match
              case enrichment: Enrichment.Base[?, ?] => enrichment.asEnrichment(instance).isDefined
              case _ => false
            }
          }
          self.withEnrichments(filtered ++ enrichments)
        else
          self
      }

    def withoutInfo(enrichments: Enrichment.Base[?, ?]*): Enriched =
      var removed = false
      val filtered = self.enrichments filterNot { instance =>
        val isInstance = enrichments exists { _.asEnrichment(instance).isDefined }
        if isInstance then removed = true
        isInstance
      }
      if removed then self.withEnrichments(filtered) else self

    def withIntrinsicInfo[E <: Enrichment[?]]
        (enrichment: Enrichment.Intrinsic[Enriched, E]): (Enriched, E) =
      self.info(enrichment) match
        case Some(enrichment) =>
          self -> enrichment
        case _ =>
          let(enrichment.make(self)) { (enriched, enrichment) =>
            enriched.withEnrichments(enrichment :: enriched.enrichments) -> enrichment
          }

    def withExtrinsicInfo[E <: Enrichment[F], F <: Enrichment.Extrinsic[? >: Enriched, E] & Singleton: ValueOf]
        (enrichment: E): Enriched =
      let(self.withoutInfo(valueOf[F])) { self =>
        self.withEnrichments(enrichment :: self.enrichments)
      }
  end extension

  extension [Enriched <: Enrichable[Enriched]](self: List[Enriched])
    def info[E](enrichment: Enrichment.Base[?, E]): List[Option[E]] =
      self map { _.info(enrichment) }
    def withInfo(enriched: Enrichable.Any): List[Enriched] =
      self map { _.withInfo(enriched) }
    def withoutInfo(enrichment: Enrichment.Base[?, ?]): List[Enriched] =
      self map { _.withoutInfo(enrichment) }
    def withIntrinsicInfo[E <: Enrichment[?]]
        (enrichment: Enrichment.Intrinsic[Enriched, E]): (List[Enriched], List[E]) =
      (self map { _.withIntrinsicInfo(enrichment) }).unzip
    def withExtrinsicInfo[E <: Enrichment[F], F <: Enrichment.Extrinsic[Enriched, E] & Singleton: ValueOf]
        (enrichment: E): List[Enriched] =
      self map { _.withExtrinsicInfo(enrichment) }
  end extension
end Enrichable


trait Enrichment[F <: Singleton](private val enrichment: F):
  private inline def enrichmentAny: Any = enrichment

object Enrichment:
  type Any = Enrichment[?]

  extension (self: Enrichment[?])
    def enrichment = self.enrichmentAny

  sealed trait Base[Enriched <: Enrichable[Enriched]: Typeable, E: Typeable]:
    def asEnrichment(enrichment: Enrichment.Any): Option[E] = enrichment match
      case enrichment: E => Some(enrichment)
      case _ => None

    def asEnriched(enriched: Enrichable.Any): Option[Enriched] = enriched match
      case enriched: Enriched => Some(enriched)
      case _ => None

  trait Extrinsic[Enriched <: Enrichable[Enriched], E] extends Base[Enriched, E]

  trait Intrinsic[Enriched <: Enrichable[Enriched], E] extends Base[Enriched, E]:
    def make(enriched: Enriched): (Enriched, E)
end Enrichment


type Enrichments = List[Enrichment.Any]

object Enrichments:
  def filter(template: Enrichable.Any, enrichments: Enrichments): Enrichments =
    enrichments flatMap { instance =>
      val keep = instance.enrichment match
        case enrichment: Enrichment.Extrinsic[?, ?] => enrichment.asEnriched(template).isDefined
        case _ => false
      Option.when(keep)(instance)
    }
