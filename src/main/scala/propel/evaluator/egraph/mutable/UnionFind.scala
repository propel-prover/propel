package propel.evaluator.egraph.mutable

import propel.evaluator.egraph.Element

import collection.mutable.{Map as MutableMap, Set as MutableSet}

/** Definition of a mutable unionfind. */
object UnionFind:
  /**
   * @param other the specified [[UnionFind UnionFind]].
   * @tparam E the type of elements of the specified [[UnionFind UnionFind]].
   * @return a copy of the specified [[UnionFind UnionFind]].
   */
  def clone[E <: Element](other: UnionFind[E]): UnionFind[E] =
    BasicUnionFind(
      universeMap = other.universeMap.clone(),
      parentMap = other.parentMap.clone(),
      heightMap = other.heightMap.clone()
    )
  /** Alias for [[empty]]. */
  def apply[E <: Element](): UnionFind[E] = UnionFind.empty[E]
  /**
   * @tparam E the specified type of [[Element]]s.
   * @return an empty union-find for the specified type of [[Element]]s.
   */
  def empty[E <: Element]: UnionFind[E] = BasicUnionFind[E]()

  /** A union-find data structure. */
  opaque type UnionFind[E <: Element] = BasicUnionFind[E]
  given UnionFindOps: UnionFindOps[UnionFind] = BasicUnionFindOps

  /** Basic implementation of a union-find based on hash-consing. */
  private case class BasicUnionFind[E <: Element](
    universeMap: MutableMap[Element.Id, E] = MutableMap[Element.Id, E](),
    parentMap: MutableMap[Element.Id, Element.Id] = MutableMap(),
    heightMap: MutableMap[Element.Id, Int] = MutableMap()
  ):
    override def toString: String =
      s"""UnionFind:
        | universe: ${universeMap.values}
        | parents: $parentMap
        | heights: $heightMap
        |""".stripMargin

  private given BasicUnionFindOps: UnionFindOps[BasicUnionFind] with
    extension[E <: Element](self: BasicUnionFind[E]) {
      override def universe: Set[E] = self.universeMap.values.toSet

      override def union(x: E, y: E): E =
        val x0 = self.find(x)
        val y0 = self.find(y)
        // always put the shortest tree under the tallest tree when merging
        if self.heightMap(x0.id) >= self.heightMap(y0.id)
        then self.setParent(y0, x0)
        else self.setParent(x0, y0)

      override def find(x: E): E =
        self.parentMap.get(x.id) match
          // x is canonical --> return x
          case Some(xParentId) if x.id == xParentId => x
          // x has a parent --> recurse on the parent and compress the tree
          case Some(xParentId) =>
            self.setParent(x, self.find(self.universeMap(xParentId)))
          // x is a new element --> set x as canonical and return it
          case _ =>
            self.universeMap.update(x.id, x)
            self.parentMap.update(x.id, x.id)
            self.heightMap.update(x.id, 0)
            x

      override def congruent(x: E, y: E): Boolean = self.find(x).id == self.find(y).id

      /**
       * Set the parent of the specified child [[Element]] to the
       * specified parent [[Element]].
       * @param child the specified child [[Element]].
       * @param parent the specified parent [[Element]].
       * @return the specified parent [[Element]].
       */
      private inline def setParent(child: E, parent: E): E =
        val ch = self.heightMap(child.id)
        val ph = self.heightMap(parent.id)
        self.parentMap.update(child.id, parent.id)
        if ch >= ph then self.heightMap.update(parent.id, ch + 1)
        parent
    }

// sbt "runMain propel.evaluator.egraph.mutable.testUnionFind"
@main def testUnionFind(): Unit =
  /** Define your own universe set. */
  case class E(name: String) extends Element:
    override def id: Element.Id = Symbol(name)

  /** Test the unionfind implementation on that set */
  val uf = UnionFind[E]()
  val (a, b, c, d, e, f, g, h) = (E("a"), E("b"), E("c"), E("d"), E("e"), E("f"), E("g"), E("h"))
  uf.union(a, b)
  uf.union(b, f)
  uf.union(f, g)
  uf.union(h, h)
  uf.union(c, d)
  uf.union(b, e)
  println(Seq(a, b, c, d, e, f, g, h).map(uf.find).mkString(" "))
  println(uf)
