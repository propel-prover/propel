package propel
package evaluator
package properties

import ast.*
import scala.collection.immutable.ListMap


val propertiesChecking = ListMap(
  Reflexive -> reflexivity,
  Irreflexive -> irreflexivity,
  Antisymmetric -> antisymmetry,
  Symmetric -> symmetry,
  Connected -> connectivity,
  Transitive -> transitivity,
  Commutative -> commutativity,
  Associative -> associativity,
  Idempotent -> idempotence,
  Selection -> selectivity)

def desugar(properties: Properties) =
  if properties contains Asymmetric then
    properties - Asymmetric + Antisymmetric + Irreflexive
  else
    properties

val derivingSimple = (propertiesChecking.values collect { case property: PropertyChecking.Simple => property.deriveSimple }).toList

val derivingCompound = (propertiesChecking.values collect { case property: PropertyChecking.Compound => property.deriveCompound }).toList

val normalizing = (propertiesChecking.values collect { case property: PropertyChecking.Normal => property.normalize }).toList

val selecting = (propertiesChecking.values collect { case property: PropertyChecking.Selecting => property.select }).toList


object reflexivity
    extends PropertyChecking with PropertyChecking.RelationTrueResult
    with PropertyChecking.Normal with PropertyChecking.Simple:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    subst(expr, Map(ident0 -> varA, ident1 -> varA)) -> Equalities.empty

  def normalize(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case App(_, App(properties, expr, arg0), arg1)
        if properties.contains(Reflexive) &&
           equalities.equal(arg0, arg1) == Equality.Equal &&
           canApply(ensureDecreasing, equalities, Reflexive)(expr)(varA, arg0, varA, arg1) =>
      Data(Constructor.True, List())

  def deriveSimple(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case App(_, App(properties, expr, arg0), arg1) -> Data(Constructor.False, List())
        if properties.contains(Reflexive) &&
           canApply(ensureDecreasing, equalities, Reflexive)(expr)(varA, arg0, varA, arg1) =>
      Equalities.neg(List(List(arg0 -> arg1))).toList
end reflexivity


object irreflexivity
    extends PropertyChecking with PropertyChecking.RelationTrueResult
    with PropertyChecking.Normal with PropertyChecking.Simple:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    subst(not(expr), Map(ident0 -> varA, ident1 -> varA)) -> Equalities.empty

  def normalize(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case App(_, App(properties, expr, arg0), arg1)
        if properties.contains(Irreflexive) &&
           equalities.equal(arg0, arg1) == Equality.Equal &&
           canApply(ensureDecreasing, equalities, Irreflexive)(expr)(varA, arg0, varA, arg1) =>
      Data(Constructor.False, List())

  def deriveSimple(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case App(_, App(properties, expr, arg0), arg1) -> Data(Constructor.True, List())
        if properties.contains(Irreflexive) &&
           canApply(ensureDecreasing, equalities, Irreflexive)(expr)(varA, arg0, varA, arg1) =>
      Equalities.neg(List(List(arg0 -> arg1))).toList
end irreflexivity


object antisymmetry
    extends PropertyChecking with PropertyChecking.RelationTrueResult
    with PropertyChecking.Simple with PropertyChecking.Compound:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val ab = subst(expr, Map(ident0 -> varA, ident1 -> varB))
    val ba = subst(expr, Map(ident0 -> varB, ident1 -> varA))
    implies(ab, not(ba)) -> Equalities.neg(List(List(varA -> varB))).get

  def deriveCompound(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case (App(_, App(properties0, expr0, arg0a), arg0b) -> Data(Constructor.True, List()),
          App(_, App(properties1, expr1, arg1a), arg1b) -> Data(Constructor.True, List()))
        if properties0.contains(Antisymmetric) &&
           properties1.contains(Antisymmetric) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           equalities.equal(arg0a, arg1b) == Equality.Equal &&
           equalities.equal(arg0b, arg1a) == Equality.Equal &&
           canApply(ensureDecreasing, equalities, Antisymmetric)(expr0)(varA, arg0a, varB, arg0b) &&
           canApply(ensureDecreasing, equalities, Antisymmetric)(expr1)(varB, arg1a, varA, arg1b) =>
      Equalities.pos(List(arg0a -> arg0b)).toList

  def deriveSimple(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case App(props, App(properties, expr, arg0), arg1) -> Data(Constructor.True, List())
        if properties.contains(Antisymmetric) &&
           canApply(ensureDecreasing, equalities, Antisymmetric)(expr)(varA, arg0, varB, arg1) =>
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

  def deriveSimple(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case App(props, App(properties, expr, arg0), arg1) -> Data(Constructor.True, List())
        if properties.contains(Symmetric) &&
           canApply(ensureDecreasing, equalities, Symmetric)(expr)(varA, arg0, varB, arg1) =>
      Equalities.pos(List(App(props, App(properties, expr, arg1), arg0) -> Data(Constructor.True, List()))).toList
    case App(props, App(properties, expr, arg0), arg1) -> Data(Constructor.False, List())
        if properties.contains(Symmetric) &&
           canApply(ensureDecreasing, equalities, Symmetric)(expr)(varA, arg0, varB, arg1) =>
      Equalities.pos(List(App(props, App(properties, expr, arg1), arg0) -> Data(Constructor.False, List()))).toList
end symmetry


object connectivity
    extends PropertyChecking with PropertyChecking.RelationTrueResult
    with PropertyChecking.Simple with PropertyChecking.Compound:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val ab = subst(expr, Map(ident0 -> varA, ident1 -> varB))
    val ba = subst(expr, Map(ident0 -> varB, ident1 -> varA))
    or(ab, ba) -> Equalities.neg(List(List(varA -> varB))).get

  def deriveCompound(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case (App(_, App(properties0, expr0, arg0a), arg0b) -> Data(Constructor.False, List()),
          App(_, App(properties1, expr1, arg1a), arg1b) -> Data(Constructor.False, List()))
        if properties0.contains(Connected) &&
           properties1.contains(Connected) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           equalities.equal(arg0a, arg1b) == Equality.Equal &&
           equalities.equal(arg0b, arg1a) == Equality.Equal &&
           canApply(ensureDecreasing, equalities, Connected)(expr0)(varB, arg0a, varA, arg0b) &&
           canApply(ensureDecreasing, equalities, Connected)(expr1)(varA, arg1a, varB, arg1b) =>
      Equalities.pos(List(arg0a -> arg0b)).toList

  def deriveSimple(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case App(props, App(properties, expr, arg0), arg1) -> Data(Constructor.False, List())
        if properties.contains(Connected) &&
           canApply(ensureDecreasing, equalities, Connected)(expr)(varA, arg0, varB, arg1) =>
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

  def deriveCompound(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case (App(props0, App(properties0, expr0, arg0a), arg0b) -> Data(Constructor.True, List()),
          App(props1, App(properties1, expr1, arg1a), arg1b) -> Data(Constructor.True, List()))
        if properties0.contains(Transitive) &&
           properties1.contains(Transitive) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           equalities.equal(arg0b, arg1a) == Equality.Equal &&
           canApply(ensureDecreasing, equalities, Transitive)(expr0)(varA, arg0a, varB, arg0b) &&
           canApply(ensureDecreasing, equalities, Transitive)(expr1)(varB, arg1a, varC, arg1b) =>
      Equalities.pos(List(App(props0, App(properties0, expr0, arg0a), arg1b) -> Data(Constructor.True, List()))).toList
    case (App(props0, App(properties0, expr0, arg0a), arg0b) -> Data(Constructor.True, List()),
          App(props1, App(properties1, expr1, arg1a), arg1b) -> Data(Constructor.True, List()))
        if properties0.contains(Transitive) &&
           properties1.contains(Transitive) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           equalities.equal(arg1b, arg0a) == Equality.Equal &&
           canApply(ensureDecreasing, equalities, Transitive)(expr0)(varB, arg0a, varC, arg0b) &&
           canApply(ensureDecreasing, equalities, Transitive)(expr1)(varA, arg1a, varB, arg1b) =>
      Equalities.pos(List(App(props0, App(properties0, expr0, arg1a), arg0b) -> Data(Constructor.True, List()))).toList
end transitivity


object commutativity
    extends PropertyChecking with PropertyChecking.FunctionEqualResult
    with PropertyChecking.Normal:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val ab = subst(expr, Map(ident0 -> varA, ident1 -> varB))
    val ba = subst(expr, Map(ident0 -> varB, ident1 -> varA))
    Data(equalDataConstructor, List(ab, ba)) -> Equalities.empty

  def normalize(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case App(props, App(properties, expr, arg0), arg1)
        if properties.contains(Commutative) &&
           canApply(ensureDecreasing, equalities, Commutative)(expr)(varA, arg0, varB, arg1) =>
      App(props, App(properties, expr, arg1), arg0)
end commutativity


object associativity
    extends PropertyChecking with PropertyChecking.FunctionEqualResult
    with PropertyChecking.Normal:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val a_bc = subst(expr, Map(ident0 -> varA, ident1 -> subst(expr, Map(ident0 -> varB, ident1 -> varC))))
    val ab_c = subst(expr, Map(ident0 -> subst(expr, Map(ident0 -> varA, ident1 -> varB)), ident1 -> varC))
    Data(equalDataConstructor, List(a_bc, ab_c)) -> Equalities.empty

  def normalize(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case App(props0, App(properties0, expr0, arg0), App(props1, App(properties1, expr1, arg1), arg2))
        if properties0.contains(Associative) &&
           properties1.contains(Associative) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           canApply(ensureDecreasing, Associative, expr0) { decreasingArguments =>
             val varWeightA = argWeight(varA, equalities)
             val varWeightB = argWeight(varB, equalities)
             val varWeightC = argWeight(varC, equalities)
             val argWeight0 = Weight(arg0)
             val argWeight1 = Weight(arg1)
             val argWeight2 = Weight(arg2)
             def associativeDecreasing =
               decreasing(decreasingArguments)(varWeightA, argWeight0, secondDecreasing = false) ||
               decreasing(decreasingArguments)(varWeightA, argWeight0, secondDecreasing = true) &&
               decreasing(decreasingArguments)(varWeightB, argWeight1, varWeightC, argWeight2)
             def associativeCommutativeDecreasing =
               properties0.contains(Commutative) &&
               properties1.contains(Commutative) &&
               canApply(ensureDecreasing, Commutative, expr0) { decreasingArguments =>
                 decreasing(decreasingArguments)(varWeightA, argWeight0, secondDecreasing = true) &&
                 decreasing(decreasingArguments)(varWeightC, argWeight1, varWeightB, argWeight2) ||
                 decreasing(decreasingArguments)(firstDecreasing = false, varWeightC, argWeight0) ||
                 decreasing(decreasingArguments)(firstDecreasing = true, varWeightC, argWeight0) &&
                 (decreasing(decreasingArguments)(varWeightA, argWeight1, varWeightB, argWeight2) ||
                  decreasing(decreasingArguments)(varWeightB, argWeight1, varWeightA, argWeight2))
               }
             associativeDecreasing || associativeCommutativeDecreasing
           } =>
      App(props0, App(properties0, expr0, App(props1, App(properties1, expr1, arg0), arg1)), arg2)
    case App(props0, App(properties0, expr0, App(props1, App(properties1, expr1, arg0), arg1)), arg2)
        if properties0.contains(Associative) &&
           properties1.contains(Associative) &&
           equalities.equal(expr0, expr1) == Equality.Equal &&
           canApply(ensureDecreasing, Associative, expr0) { decreasingArguments =>
             val varWeightA = argWeight(varA, equalities)
             val varWeightB = argWeight(varB, equalities)
             val varWeightC = argWeight(varC, equalities)
             val argWeight0 = Weight(arg0)
             val argWeight1 = Weight(arg1)
             val argWeight2 = Weight(arg2)
             def associativeDecreasing =
               decreasing(decreasingArguments)(firstDecreasing = false, varWeightC, argWeight2) ||
               decreasing(decreasingArguments)(firstDecreasing = true, varWeightC, argWeight2) &&
               decreasing(decreasingArguments)(varWeightA, argWeight0, varWeightB, argWeight1)
             def associativeCommutativeDecreasing =
               properties0.contains(Commutative) &&
               properties1.contains(Commutative) &&
               canApply(ensureDecreasing, Commutative, expr0) { decreasingArguments =>
                 decreasing(decreasingArguments)(firstDecreasing = true, varWeightC, argWeight2) &&
                 decreasing(decreasingArguments)(varWeightB, argWeight0, varWeightA, argWeight1) ||
                 decreasing(decreasingArguments)(varWeightA, argWeight2, secondDecreasing = false) ||
                 decreasing(decreasingArguments)(varWeightA, argWeight2, secondDecreasing = true) &&
                 (decreasing(decreasingArguments)(varWeightB, argWeight0, varWeightC, argWeight1) ||
                  decreasing(decreasingArguments)(varWeightC, argWeight0, varWeightB, argWeight1))
               }
             associativeDecreasing || associativeCommutativeDecreasing
           } =>
      App(props0, App(properties0, expr0, arg0), App(props1, App(properties1, expr1, arg1), arg2))
end associativity


object idempotence
    extends PropertyChecking with PropertyChecking.FunctionEqualResult
    with PropertyChecking.Normal:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    val aa = subst(expr, Map(ident0 -> varA, ident1 -> varA))
    Data(equalDataConstructor, List(aa, varA)) -> Equalities.empty

  def normalize(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case term @ App(_, App(properties, expr, arg0), arg1)
        if properties.contains(Idempotent) &&
           equalities.equal(arg0, arg1) == Equality.Equal &&
           canApply(ensureDecreasing, equalities, Idempotent)(expr)(varA, arg0, varA, arg1) =>
      arg0
end idempotence


object selectivity
    extends PropertyChecking with PropertyChecking.FunctionSelectionResult
    with PropertyChecking.Selecting:
  def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
    Data(resultDataConstructor, List(subst(expr, Map(ident0 -> varA, ident1 -> varB)))) ->
      Equalities.pos(List(Var(ident0) -> varA, Var(ident1) -> varB)).get

  def select(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities) =
    case term @ App(_, App(properties, expr, arg0), arg1)
        if properties.contains(Selection) &&
           canApply(ensureDecreasing, equalities, Selection)(expr)(varA, arg0, varB, arg1) =>
    (Equalities.pos(List(term -> arg0, arg0 -> arg1)).toList map { arg0 -> _ }) ++
    (Equalities.make(List(term -> arg0), List(List(arg0 -> arg1))).toList map { arg0 -> _ }) ++
    (Equalities.make(List(term -> arg1), List(List(arg0 -> arg1))).toList map { arg1 -> _ })
end selectivity
