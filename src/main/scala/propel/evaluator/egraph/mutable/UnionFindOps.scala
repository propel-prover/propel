package propel.evaluator.egraph.mutable

import propel.evaluator.egraph.Element

/** A type-class defining the operations supported by a union-find. */
trait UnionFindOps[UnionFind[_ <: Element]]:
  extension[E <: Element] (self: UnionFind[E]) {
    /** @return the set of all known [[Element]]s. */
    def universe: Set[E]
    /**
     * Merge the partitions of the two specified [[Element]]s into a new partition.
     * @param x the first specified [[Element]].
     * @param y the second specified [[Element]].
     * @return the canonical [[Element]] of the new partition.
     */
    def union(x: E, y: E): E
    /**
     * @param x the specified [[Element]].
     * @return the canonical [[Element]] of the partition to which the specified
     *         [[Element]] belongs.
     */
    def find(x: E): E
    /**
     * @param x the first specified [[Element]].
     * @param y the second specified [[Element]].
     * @return [[true]] if the specified [[Element]]s belong to the same partition;
     *         [[false]] otherwise.
     */
    def congruent(x: E, y: E): Boolean
  }
