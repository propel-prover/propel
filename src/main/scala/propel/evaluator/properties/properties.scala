package propel
package evaluator
package properties

import ast.*
import scala.collection.immutable.ListMap


val propertiesChecking = ListMap(
  Reflexive -> reflexivity,
  Antisymmetric -> antisymmetry,
  Symmetric -> symmetry,
  Connected -> connectivity,
  Transitive -> transitivity,
  Commutative -> commutativity,
  Associative -> associativity,
  Selection -> selectivity)

val derivingSimple = (propertiesChecking.values collect { case property: PropertyChecking.Simple => property.deriveSimple }).toList

val derivingCompound = (propertiesChecking.values collect { case property: PropertyChecking.Compound => property.deriveCompound }).toList

val normalizing = (propertiesChecking.values collect { case property: PropertyChecking.Normal => property.normalize }).toList

val selecting = (propertiesChecking.values collect { case property: PropertyChecking.Selecting => property.select }).toList


object reflexivity
    extends PropertyChecking with PropertyChecking.RelationTrueResult
    with PropertyChecking.Normal:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    subst(expr, Map(ident0 -> varA, ident1 -> varA)) -> Equalities.empty

  def normalize(equalities: Equalities) =
    case App(props, App(properties, expr, arg0), arg1)
        if properties.contains(Reflexive) &&
           equalities.equal(arg0, arg1) == Equality.Equal =>
      Data(Constructor.True, List())
end reflexivity


object antisymmetry
    extends PropertyChecking with PropertyChecking.RelationTrueResult
    with PropertyChecking.Simple with PropertyChecking.Compound:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val ab = subst(expr, Map(ident0 -> varA, ident1 -> varB))
    val ba = subst(expr, Map(ident0 -> varB, ident1 -> varA))
    implies(ab, not(ba)) -> Equalities.neg(List(List(varA -> varB))).get

  def deriveCompound(equalities: Equalities) =
    case (App(_, App(properties0, expr0, arg0a), arg0b) -> Data(Constructor.True, List()),
          App(_, App(properties1, expr1, arg1a), arg1b) -> Data(Constructor.True, List()))
        if properties0.contains(Antisymmetric) &&
           properties1.contains(Antisymmetric) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           equalities.equal(arg0a, arg1b) == Equality.Equal &&
           equalities.equal(arg0b, arg1a) == Equality.Equal =>
      Equalities.pos(List(arg0a -> arg0b)).toList

  def deriveSimple(equalities: Equalities) =
    case App(props, App(properties, expr, arg0), arg1) -> Data(Constructor.True, List())
        if properties.contains(Antisymmetric) =>
      Equalities.pos(List(arg0 -> arg1)).toList ++
      Equalities.make(List(App(props, App(properties, expr, arg1), arg0) -> Data(Constructor.False, List())), List(List(arg0 -> arg1))).toList
end antisymmetry


object symmetry
    extends PropertyChecking with PropertyChecking.RelationTrueResult
    with PropertyChecking.Simple:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val ab = subst(expr, Map(ident0 -> varA, ident1 -> varB))
    val ba = subst(expr, Map(ident0 -> varB, ident1 -> varA))
    implies(ab, ba) -> Equalities.empty

  def deriveSimple(equalities: Equalities) =
    case App(props, App(properties, expr, arg0), arg1) -> Data(Constructor.True, List())
        if properties.contains(Symmetric) =>
      Equalities.pos(List(App(props, App(properties, expr, arg1), arg0) -> Data(Constructor.True, List()))).toList
end symmetry


object connectivity
    extends PropertyChecking with PropertyChecking.RelationTrueResult
    with PropertyChecking.Simple with PropertyChecking.Compound:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val ab = subst(expr, Map(ident0 -> varA, ident1 -> varB))
    val ba = subst(expr, Map(ident0 -> varB, ident1 -> varA))
    or(ab, ba) -> Equalities.neg(List(List(varA -> varB))).get

  def deriveCompound(equalities: Equalities) =
    case (App(_, App(properties0, expr0, arg0a), arg0b) -> Data(Constructor.False, List()),
          App(_, App(properties1, expr1, arg1a), arg1b) -> Data(Constructor.False, List()))
        if properties0.contains(Connected) &&
           properties1.contains(Connected) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           equalities.equal(arg0a, arg1b) == Equality.Equal &&
           equalities.equal(arg0b, arg1a) == Equality.Equal =>
      Equalities.pos(List(arg0a -> arg0b)).toList

  def deriveSimple(equalities: Equalities) =
    case App(props, App(properties, expr, arg0), arg1) -> Data(Constructor.False, List())
        if properties.contains(Connected) =>
      Equalities.pos(List(arg0 -> arg1)).toList ++
      Equalities.make(List(App(props, App(properties, expr, arg1), arg0) -> Data(Constructor.True, List())), List(List(arg0 -> arg1))).toList
end connectivity


object transitivity
    extends PropertyChecking with PropertyChecking.RelationTrueResult
    with PropertyChecking.Compound:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val ab = subst(expr, Map(ident0 -> varA, ident1 -> varB))
    val bc = subst(expr, Map(ident0 -> varB, ident1 -> varC))
    val ac = subst(expr, Map(ident0 -> varA, ident1 -> varC))
    implies(and(ab, bc), ac) -> Equalities.empty

  def deriveCompound(equalities: Equalities) =
    case (App(props0, App(properties0, expr0, arg0a), arg0b) -> Data(Constructor.True, List()),
          App(props1, App(properties1, expr1, arg1a), arg1b) -> Data(Constructor.True, List()))
        if properties0.contains(Transitive) &&
           properties1.contains(Transitive) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           equalities.equal(arg0b, arg1a) == Equality.Equal =>
      Equalities.pos(List(App(props0, App(properties0, expr0, arg0a), arg1b) -> Data(Constructor.True, List()))).toList
    case (App(props0, App(properties0, expr0, arg0a), arg0b) -> Data(Constructor.True, List()),
          App(props1, App(properties1, expr1, arg1a), arg1b) -> Data(Constructor.True, List()))
        if properties0.contains(Transitive) &&
           properties1.contains(Transitive) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           equalities.equal(arg1b, arg0a) == Equality.Equal =>
      Equalities.pos(List(App(props0, App(properties0, expr0, arg1a), arg0b) -> Data(Constructor.True, List()))).toList
end transitivity


object commutativity
    extends PropertyChecking with PropertyChecking.FunctionEqualResult
    with PropertyChecking.Normal:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val ab = subst(expr, Map(ident0 -> varA, ident1 -> varB))
    val ba = subst(expr, Map(ident0 -> varB, ident1 -> varA))
    Data(equalDataConstructor, List(ab, ba)) -> Equalities.empty

  def normalize(equalities: Equalities) =
    case App(props, App(properties, expr, arg0), arg1)
        if properties.contains(Commutative) =>
      App(props, App(properties, expr, arg1), arg0)
end commutativity


object associativity
    extends PropertyChecking with PropertyChecking.FunctionEqualResult
    with PropertyChecking.Normal:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val a_bc = subst(expr, Map(ident0 -> varA, ident1 -> subst(expr, Map(ident0 -> varB, ident1 -> varC))))
    val ab_c = subst(expr, Map(ident0 -> subst(expr, Map(ident0 -> varA, ident1 -> varB)), ident1 -> varC))
    Data(equalDataConstructor, List(a_bc, ab_c)) -> Equalities.empty

  def normalize(equalities: Equalities) =
    case App(props0, App(properties0, expr0, arg0), App(props1, App(properties1, expr1, arg1), arg2))
        if properties0.contains(Associative) &&
           properties1.contains(Associative) &&
           equalities.equal(expr0, expr1) == Equality.Equal =>
      App(props0, App(properties0, expr0, App(props1, App(properties1, expr1, arg0), arg1)), arg2)
    case App(props0, App(properties0, expr0, App(props1, App(properties1, expr1, arg0), arg1)), arg2)
        if properties0.contains(Associative) &&
           properties1.contains(Associative) &&
           equalities.equal(expr0, expr1) == Equality.Equal =>
      App(props0, App(properties0, expr0, arg0), App(props1, App(properties1, expr1, arg1), arg2))
end associativity


object selectivity
    extends PropertyChecking with PropertyChecking.FunctionSelectionResult
    with PropertyChecking.Selecting:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    Data(resultDataConstructor, List(expr)) -> Equalities.empty

  def select(equalities: Equalities) =
    case expr @ App(props, App(properties, _, arg0), arg1)
        if properties.contains(Selection) =>
    (Equalities.pos(List(expr -> arg0, arg0 -> arg1)).toList map { arg0 -> _ }) ++
    (Equalities.make(List(expr -> arg0), List(List(arg0 -> arg1))).toList map { arg0 -> _ }) ++
    (Equalities.make(List(expr -> arg1), List(List(arg0 -> arg1))).toList map { arg1 -> _ })
end selectivity
