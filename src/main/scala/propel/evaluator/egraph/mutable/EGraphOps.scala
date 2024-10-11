package propel.evaluator.egraph.mutable

import propel.evaluator.egraph.{EClass, ENode}

/** A type-class defining the operations supported by an e-graph. */
trait EGraphOps[EGraph]:
  extension (self: EGraph) {
    /** @return a map from [[EClass]]es to the sets of their [[ENode]]es. */
    def eclasses: Map[EClass, Set[ENode]]
    /**
     * Add the specified [[ENode]] to this e-graph.
     * @param x the specified [[ENode]].
     * @return the [[EClass]] of the specified [[ENode]].
     * @note the hash-cons invariant may be broken after a call
     *       to this method.
     */
    def add(x: ENode): EClass
    /**
     * Merge the specified [[EClass]]es into a new [[EClass]].
     * @param xc the first specified [[EClass]].
     * @param yc the second specified [[EClass]].
     * @return the new [[EClass]].
     * @note the hash-cons and congruence invariants may be broken
     *       after a call to this method.
     */
    def union(xc: EClass, yc: EClass): EClass
    /**
     * Add a inequality edge between the two specified [[EClass]]es.
     * @param xc the first specified [[EClass]].
     * @param yc the second specified [[EClass]].
     */
    def disunion(xc: EClass, yc: EClass): Unit
    /**
     * @param xc the specified [[EClass]].
     * @return the canonical [[EClass]] representing the specified
     *         [[EClass]].
     */
    def find(xc: EClass): EClass
    /**
     * @param xc the first specified [[EClass]].
     * @param yc the second specified [[EClass]].
     * @return [[true]] if the two specified [[EClass]]es are equivalent;
     *         [[false]] otherwise.
     */
    def equal(xc: EClass, yc: EClass): Boolean
    /**
     * @param xc the first specified [[EClass]].
     * @param yc the second specified [[EClass]].
     * @return [[true]] if there exist a inequality edge between the
     *         two specified [[EClass]]es; [[false]] otherwise.
     */
    def unequal(xc: EClass, yc: EClass): Boolean
    /** Restore the hash-cons and congruence invariance in this e-graph. */
    def rebuild(): Unit
    /**
     * @param x the specified [[ENode]].
     * @return an equivalent [[ENode]] referencing only canonical [[EClass]]es.
     */
    def canonicalize(x: ENode): ENode
    /** 
     * @return [[true]] if any two [[EClass]]es are both [[equal]] and [[unequal]];
     *         [[false]] otherwise.
     */
    def hasContradiction: Boolean
  }
