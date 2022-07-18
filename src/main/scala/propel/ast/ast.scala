package propel
package ast

export Property.*
export Pattern.*
export Term.*


type Properties = Set[Property]

enum Property:
  case Commutative
  case Associative
  case Idempotent
  case Reflexive
  case Irreflexive
  case Symmetric
  case Antisymmetric
  case Asymmetric
  case Connected
  case Transitive


case class Constructor(ident: Symbol)

object Constructor:
  val False = Constructor(Symbol("⊥"))
  val True = Constructor(Symbol("⊤"))


sealed trait Pattern extends Enrichable[Pattern]:
  protected def withEnrichment(pattern: Pattern, enrichments: Enrichments) = pattern match
    case Match(ctor, args) => Match(ctor, args)(enrichments)
    case Bind(ident) => Bind(ident)(enrichments)

object Pattern:
  case class Match private[Pattern] (ctor: Constructor, args: List[Pattern]) (val enrichments: Enrichments) extends Pattern

  object Match:
    def apply(ctor: Constructor, args: List[Pattern]): Match = impl.defaultApply
    def apply(template: Pattern)(ctor: Constructor, args: List[Pattern]): Match = impl.defaultApply

  case class Bind private[Pattern] (ident: Symbol) (val enrichments: Enrichments) extends Pattern

  object Bind:
    def apply(ident: Symbol): Bind = impl.defaultApply
    def apply(template: Pattern)(ident: Symbol): Bind = impl.defaultApply


sealed trait Term extends Enrichable[Term]:
  protected def withEnrichment(expr: Term, enrichments: Enrichments) = expr match
    case Abs(properties, ident, expr) => Abs(properties, ident, expr)(enrichments)
    case App(properties, expr, arg) => App(properties, expr, arg)(enrichments)
    case Data(ctor, args) => Data(ctor, args)(enrichments)
    case Var(ident) => Var(ident)(enrichments)
    case Cases(scrutinee, cases) => Cases(scrutinee, cases)(enrichments)

object Term:
  case class Abs private[Term] (properties: Properties, ident: Symbol, expr: Term) (val enrichments: Enrichments) extends Term

  object Abs:
    def apply(properties: Properties, ident: Symbol, expr: Term): Abs = impl.defaultApply
    def apply(template: Term)(properties: Properties, ident: Symbol, expr: Term): Abs = impl.defaultApply

  case class App private[Term] (properties: Properties, expr: Term, arg: Term) (val enrichments: Enrichments) extends Term

  object App:
    def apply(properties: Properties, expr: Term, arg: Term): App = impl.defaultApply
    def apply(template: Term)(properties: Properties, expr: Term, arg: Term): App = impl.defaultApply

  case class Data private[Term] (ctor: Constructor, args: List[Term]) (val enrichments: Enrichments) extends Term

  object Data:
    def apply(ctor: Constructor, args: List[Term]): Data = impl.defaultApply
    def apply(template: Term)(ctor: Constructor, args: List[Term]): Data = impl.defaultApply

  case class Var private[Term] (ident: Symbol) (val enrichments: Enrichments) extends Term

  object Var:
    def apply(ident: Symbol): Var = impl.defaultApply
    def apply(template: Term)(ident: Symbol): Var = impl.defaultApply

  case class Cases(scrutinee: Term, cases: List[(Pattern, Term)]) (val enrichments: Enrichments) extends Term

  object Cases:
    def apply(scrutinee: Term, cases: List[(Pattern, Term)]): Cases = impl.defaultApply
    def apply(template: Term)(scrutinee: Term, cases: List[(Pattern, Term)]): Cases = impl.defaultApply
