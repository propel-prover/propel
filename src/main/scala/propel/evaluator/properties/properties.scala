package propel
package evaluator
package properties

import ast.*


val propertiesChecking = Map(
  Antisymmetric -> antisymmetry,
  Transitive -> transitivity,
  Commutative -> commutativity,
  Associative -> associativity)

val derivingSimple = (propertiesChecking.values collect { case property: PropertyChecking.Simple => property.deriveSimple }).toList

val derivingCompound = (propertiesChecking.values collect { case property: PropertyChecking.Compound => property.deriveCompound }).toList

val normalizing = (propertiesChecking.values collect { case property: PropertyChecking.Normal => property.normalize }).toList


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
           equalities.equal(arg0b, arg1a) == Equality.Equal &&
           equalities.equal(arg0a, arg0b) != Equality.Equal =>
      arg0a -> arg0b
          
  def deriveSimple(equalities: Equalities) =
    case App(props, App(properties, expr, arg0), arg1) -> Data(Constructor.True, List())
        if properties.contains(Antisymmetric) &&
           equalities.equal(arg0, arg1) == Equality.Unequal =>
      App(props, App(properties, expr, arg1), arg0) -> Data(Constructor.False, List())
end antisymmetry


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
      App(props0, App(properties0, expr0, arg0a), arg1b) -> Data(Constructor.True, List())
    case (App(props0, App(properties0, expr0, arg0a), arg0b) -> Data(Constructor.True, List()),
          App(props1, App(properties1, expr1, arg1a), arg1b) -> Data(Constructor.True, List()))
        if properties0.contains(Transitive) &&
           properties1.contains(Transitive) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           equalities.equal(arg1b, arg0a) == Equality.Equal =>
      App(props0, App(properties0, expr0, arg1a), arg0b) -> Data(Constructor.True, List())
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
        if properties.contains(Commutative) && arg1 < arg0 =>
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
           equalities.equal(expr0, expr1) == Equality.Equal &&
           arg2 < arg0 =>
      App(props0, App(properties0, expr0, App(props1, App(properties1, expr1, arg0), arg1)), arg2)
    case App(props0, App(properties0, expr0, App(props1, App(properties1, expr1, arg0), arg1)), arg2)
        if properties0.contains(Associative) &&
           properties1.contains(Associative) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           arg0 < arg2 =>
      App(props0, App(properties0, expr0, arg0), App(props1, App(properties1, expr1, arg1), arg2))
end associativity
