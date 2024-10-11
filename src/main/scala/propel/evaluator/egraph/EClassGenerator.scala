package propel.evaluator.egraph

/** A function generating [[EClass]]es from [[ENode]]s. */
@FunctionalInterface 
trait EClassGenerator extends Function[ENode, EClass]
