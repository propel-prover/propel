package propel
package ast

export Property.*
export Pattern.*
export Type.*
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
  protected def withEnrichments(enrichments: Enrichments) = this match
    case Match(ctor, args) => Match(ctor, args)(enrichments)
    case Bind(ident) => Bind(ident)(enrichments)

object Pattern:
  case class Match private[Pattern] (ctor: Constructor, args: List[Pattern]) (val enrichments: Enrichments) extends Pattern:
    override val hashCode = impl.defaultHashCode

  object Match:
    def apply(ctor: Constructor, args: List[Pattern]): Match = impl.defaultApply
    def apply(template: Enrichable.Any)(ctor: Constructor, args: List[Pattern]): Match = impl.defaultApply

  case class Bind private[Pattern] (ident: Symbol) (val enrichments: Enrichments) extends Pattern:
    override val hashCode = impl.defaultHashCode

  object Bind:
    def apply(ident: Symbol): Bind = impl.defaultApply
    def apply(template: Enrichable.Any)(ident: Symbol): Bind = impl.defaultApply


sealed trait Type extends Enrichable[Type]:
  protected def withEnrichments(enrichments: Enrichments) = this match
    case Function(arg, result) => Function(arg, result)(enrichments)
    case Universal(ident, result) => Universal(ident, result)(enrichments)
    case Recursive(ident, result) => Recursive(ident, result)(enrichments)
    case TypeVar(ident) => TypeVar(ident)(enrichments)
    case Sum(sum) => Sum(sum)(enrichments)

object Type:
  case class Function private[Type] (arg: Type, result: Type) (val enrichments: Enrichments) extends Type:
    override val hashCode = impl.defaultHashCode

  object Function:
    def apply(arg: Type, result: Type): Function = impl.defaultApply
    def apply(template: Enrichable.Any)(arg: Type, result: Type): Function = impl.defaultApply

  case class Universal private[Type] (ident: Symbol, result: Type) (val enrichments: Enrichments) extends Type:
    override val hashCode = impl.defaultHashCode

  object Universal:
    def apply(ident: Symbol, result: Type): Universal = impl.defaultApply
    def apply(template: Enrichable.Any)(ident: Symbol, result: Type): Universal = impl.defaultApply

  case class Recursive private[Type] (ident: Symbol, result: Type) (val enrichments: Enrichments) extends Type:
    override val hashCode = impl.defaultHashCode

  object Recursive:
    def apply(ident: Symbol, result: Type): Recursive = impl.defaultApply
    def apply(template: Enrichable.Any)(ident: Symbol, result: Type): Recursive = impl.defaultApply

  case class TypeVar private[Type] (ident: Symbol) (val enrichments: Enrichments) extends Type:
    override val hashCode = impl.defaultHashCode

  object TypeVar:
    def apply(ident: Symbol): TypeVar = impl.defaultApply
    def apply(template: Enrichable.Any)(ident: Symbol): TypeVar = impl.defaultApply

  case class Sum private[Type] (sum: List[(Constructor, List[Type])]) (val enrichments: Enrichments) extends Type:
    override val hashCode = impl.defaultHashCode

  object Sum:
    def apply(sum: List[(Constructor, List[Type])]): Sum = impl.defaultApply
    def apply(template: Enrichable.Any)(sum: List[(Constructor, List[Type])]): Sum = impl.defaultApply


sealed trait Term extends Enrichable[Term]:
  protected def withEnrichments(enrichments: Enrichments) = this match
    case Abs(properties, ident, tpe, expr) => Abs(properties, ident, tpe, expr)(enrichments)
    case App(properties, expr, arg) => App(properties, expr, arg)(enrichments)
    case TypeAbs(ident, expr) => TypeAbs(ident, expr)(enrichments)
    case TypeApp(expr, tpe) => TypeApp(expr, tpe)(enrichments)
    case Data(ctor, args) => Data(ctor, args)(enrichments)
    case Var(ident) => Var(ident)(enrichments)
    case Cases(scrutinee, cases) => Cases(scrutinee, cases)(enrichments)

object Term:
  case class Abs private[Term] (properties: Properties, ident: Symbol, tpe: Type, expr: Term) (val enrichments: Enrichments) extends Term:
    override val hashCode = impl.defaultHashCode

  object Abs:
    def apply(properties: Properties, ident: Symbol, tpe: Type, expr: Term): Abs = impl.defaultApply
    def apply(template: Enrichable.Any)(properties: Properties, ident: Symbol, tpe: Type, expr: Term): Abs = impl.defaultApply

  case class App private[Term] (properties: Properties, expr: Term, arg: Term) (val enrichments: Enrichments) extends Term:
    override val hashCode = impl.defaultHashCode

  object App:
    def apply(properties: Properties, expr: Term, arg: Term): App = impl.defaultApply
    def apply(template: Enrichable.Any)(properties: Properties, expr: Term, arg: Term): App = impl.defaultApply

  case class TypeAbs private[Term] (ident: Symbol, expr: Term) (val enrichments: Enrichments) extends Term:
    override val hashCode = impl.defaultHashCode

  object TypeAbs:
    def apply(ident: Symbol, expr: Term): TypeAbs = impl.defaultApply
    def apply(template: Enrichable.Any)(ident: Symbol, expr: Term): TypeAbs = impl.defaultApply

  case class TypeApp private[Term] (expr: Term, tpe: Type) (val enrichments: Enrichments) extends Term:
    override val hashCode = impl.defaultHashCode

  object TypeApp:
    def apply(expr: Term, tpe: Type): TypeApp = impl.defaultApply
    def apply(template: Enrichable.Any)(expr: Term, tpe: Type): TypeApp = impl.defaultApply

  case class Data private[Term] (ctor: Constructor, args: List[Term]) (val enrichments: Enrichments) extends Term:
    override val hashCode = impl.defaultHashCode

  object Data:
    def apply(ctor: Constructor, args: List[Term]): Data = impl.defaultApply
    def apply(template: Enrichable.Any)(ctor: Constructor, args: List[Term]): Data = impl.defaultApply

  case class Var private[Term] (ident: Symbol) (val enrichments: Enrichments) extends Term:
    override val hashCode = impl.defaultHashCode

  object Var:
    def apply(ident: Symbol): Var = impl.defaultApply
    def apply(template: Enrichable.Any)(ident: Symbol): Var = impl.defaultApply

  case class Cases(scrutinee: Term, cases: List[(Pattern, Term)]) (val enrichments: Enrichments) extends Term:
    override val hashCode = impl.defaultHashCode

  object Cases:
    def apply(scrutinee: Term, cases: List[(Pattern, Term)]): Cases = impl.defaultApply
    def apply(template: Enrichable.Any)(scrutinee: Term, cases: List[(Pattern, Term)]): Cases = impl.defaultApply
