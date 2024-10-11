package propel.evaluator.egraph.mutable

import propel.evaluator.egraph.{EClass, EClassGenerator, ENode, Language, Operator}
import collection.mutable.{Map as MutableMap, Set as MutableSet}

/** Definition of a mutable egraph. */
object EGraph:
  /**
   * @param other the specified [[EGraph EGraph]].
   * @return a copy of the specified [[EGraph EGraph]].
   */
  def clone(other: EGraph): EGraph =
    BasicEGraph(
      underlying = UnionFind.clone(other.underlying),
      classes = other.classes.clone(),
      enodes = other.enodes.clone(),
      datas = other.datas.clone().map(_ -> _.clone()),
      worklist = other.worklist.clone(),
      contradictory = other.contradictory,
    )
  /** Alias for [[empty]]. */
  def apply(): EGraph = EGraph.empty

  /** @return an empty e-graph. */
  def empty: EGraph = BasicEGraph()

  /** An e-graph data structure. */
  opaque type EGraph = BasicEGraph

  object DisequalityEdges:
    given EGraphsOps: EGraphOps[EGraph] = new EGraph.DisequalityEdgesOps {}

  object EqualityEmbedding:
    given EGraphsOps: EGraphOps[EGraph] = new EGraph.EqualityEmbeddingOps {}

  object DisequalityEmbedding:
    given EGraphsOps: EGraphOps[EGraph] = new EGraph.DisequalityEmbeddingOps {}


  /** The mutable data of an [[EClass]]. */
  private case class EClassData():
    /** A map from [[ENode]]s referencing this [[EClass]] to their corresponding [[EClass]]. */
    var uses: MutableMap[ENode, EClass] = MutableMap()
    /** A set of [[EClass]]es connected to this [[EClass]] by an inequality edge. */
    var forbids: MutableSet[EClass.Id] = MutableSet()
    override def clone(): EClassData =
      val data = EClassData()
      data.uses = this.uses.clone()
      data.forbids = this.forbids.clone()
      data

  /** Basic implementation of an e-graph. */
  private case class BasicEGraph(
    underlying: UnionFind.UnionFind[EClass] = UnionFind(),
    classes: MutableMap[EClass.Id, EClass] = MutableMap(),
    enodes: MutableMap[ENode, EClass.Id] = MutableMap(),
    datas: MutableMap[EClass.Id, EClassData] = MutableMap(),
    worklist: MutableSet[EClass.Id] = MutableSet(),
    var contradictory: Boolean = false
  ):
    override def toString: String =
      s"""EGraph:
        | unionfind: $underlying
        | classes: $classes
        | enodes: $enodes
        | datas: $datas
        | worklist: $worklist
        | contradictory: $contradictory
        |""".stripMargin

  /** Basic operations for egraphs. */
  private trait CommonEGraphOps extends EGraphOps[BasicEGraph]:
    extension (self: BasicEGraph) {
      override def eclasses: Map[EClass, Set[ENode]] =
        self.enodes.groupBy((x, xcId) => self.find(self.classes(xcId))).map(_ -> _.toMap.keySet)
      override def add(x: ENode): EClass =
        self.lookup(x) match
          case (_, Some(xc)) => xc
          case (x0, _) =>
            val xc0 = self.find(EClass(x0))
            x0.refs.foreach(refc =>
              self.classes.update(refc.id, refc)
              self.datas.getOrElseUpdate(refc.id, EClassData()).uses.addOne(x0 -> xc0)
              self.enodes.update(refc.canonical, refc.id)
            )
            self.classes.update(xc0.id, xc0)
            self.datas.update(xc0.id, EClassData())
            self.enodes.update(x0, xc0.id)
            xc0

      override def union(xc: EClass, yc: EClass): EClass =
        val xc0 = self.find(xc)
        val yc0 = self.find(yc)
        if xc0 == yc0 then return xc0

        val xyc = self.underlying.union(xc0, yc0)
        val xycData = self.datas.getOrElseUpdate(xyc.id, EClassData())
        val other = if xyc.id == xc0.id then yc0 else xc0
        val otherData = self.datas.getOrElse(other.id, EClassData())
        xycData.uses.addAll(otherData.uses)
        self.datas.remove(other.id)
        self.contradictory ||= self.unequal(xc0, yc0)

        self.worklist.add(xyc.id)
        xyc

      override def find(xc: EClass): EClass = self.underlying.find(xc)

      override def equal(xc: EClass, yc: EClass): Boolean = self.underlying.congruent(xc, yc)

      override def rebuild(): Unit =
        def repair(xc: EClass): Unit =
          val xcData = self.datas.remove(xc.id).getOrElse(EClassData())
          // Restore universe by making all e-nodes point to canonical e-classes
          xcData.uses.foreach((x, xcStale) =>
            self.enodes.remove(x)
            self.enodes.update(self.canonicalize(x), self.find(xcStale).id)
          )
          // Remove duplicate uses
          val distinctUses = MutableMap[ENode, EClass]()
          xcData.uses.foreach((x, xcStale) =>
            val x0 = self.canonicalize(x)
            distinctUses.get(x0).foreach(xc => self.union(xcStale, xc))
            distinctUses.update(x0, self.find(xcStale))
          )
          xcData.uses = distinctUses
          self.datas.update(self.find(xc).id, xcData)

        while (self.worklist.nonEmpty) {
          val brokenClasses = self.worklist.map(id => self.find(self.classes(id)))
          self.worklist.clear()
          brokenClasses.foreach(repair)
        }

      override def canonicalize(x: ENode): ENode = ENode(x.op, x.refs.map(self.find))
      /**
       * @param x the specified e-node.
       * @return a pair containing the specified e-node canonicalized and
       *         its e-class if already known (i.e., if the e-node was
       *         already added in the past).
       */
      private def lookup(x: ENode): (ENode, Option[EClass]) =
        val x0 = self.canonicalize(x)
        (x0, self.enodes.get(x0).map(self.classes))
    }
  /** Basic operations for egraphs with disequality edges. */
  private trait DisequalityEdgesOps extends CommonEGraphOps:
    extension (self: BasicEGraph) {
      override def union(xc: EClass, yc: EClass): EClass =
        val xc0 = self.find(xc)
        val yc0 = self.find(yc)
        if xc0 == yc0 then return xc0

        val xyc = self.underlying.union(xc0, yc0)
        val xycData = self.datas.getOrElseUpdate(xyc.id, EClassData())
        val other = if xyc.id == xc0.id then yc0 else xc0
        val otherData = self.datas.getOrElse(other.id, EClassData())
        xycData.uses.addAll(otherData.uses)
        xycData.forbids.addAll(otherData.forbids)
        self.datas.remove(other.id)
        self.contradictory ||= self.unequal(xc0, yc0)

        self.worklist.add(xyc.id)
        xyc
      
      override def disunion(xc: EClass, yc: EClass): Unit =
        val xc0 = self.find(xc)
        val yc0 = self.find(yc)
        self.datas.getOrElseUpdate(xc0.id, EClassData()).forbids.addOne(yc0.id)
        self.datas.getOrElseUpdate(yc0.id, EClassData()).forbids.addOne(xc0.id)
        self.contradictory ||= xc0.id == yc0.id

      override def unequal(xc: EClass, yc: EClass): Boolean =
        val xc0 = self.find(xc)
        val yc0 = self.find(yc)
        val xc0Forbids = self.datas.getOrElse(xc0.id, EClassData()).forbids
        val yc0Forbids = self.datas.getOrElse(yc0.id, EClassData()).forbids
        val (smallForbids, large) = if xc0Forbids.size < yc0Forbids.size then (xc0Forbids, yc0) else (yc0Forbids, xc0)
        smallForbids.map(id => self.find(self.classes(id)).id)(large.id)

      override def hasContradiction: Boolean = self.contradictory
    }

  /** Basic operations for egraphs with equality embedding. */
  private trait EqualityEmbeddingOps extends CommonEGraphOps:
    private val TrueOp: Operator = Operator("@⊤")
    private val FalseOp: Operator = Operator("@⊥")
    private val EqualOp: Operator = Operator("@=")
    private val EmbeddingOps: Set[Operator] = Set(TrueOp, FalseOp, EqualOp)
    private val True: ENode = ENode(TrueOp)
    private val False: ENode = ENode(FalseOp)
    private def Equal(xc: EClass, yc: EClass): ENode = ENode(EqualOp, Seq(xc, yc))
    private def isEmbedding(x: ENode): Boolean = EmbeddingOps(x.op)
    
    extension (self: BasicEGraph){
      override def add(x: ENode): EClass =
        val xc = super.add(self)(x)
        if !EqualityEmbeddingOps.this.isEmbedding(x) then
          self.underlying.union(self.Equal(xc, xc), self.True)
        xc
      override def union(xc: EClass, yc: EClass): EClass =
        val xc0 = self.find(xc)
        val yc0 = self.find(yc)
        if xc0 == yc0 then return xc0

        val xyc = self.underlying.union(xc0, yc0)
        if !EqualityEmbeddingOps.this.isEmbedding(xc.canonical) then
          self.underlying.union(self.Equal(xc0, yc0), self.True)
          self.underlying.union(self.Equal(yc0, xc0), self.True)

        val xycData = self.datas.getOrElseUpdate(xyc.id, EClassData())
        val other = if xyc.id == xc0.id then yc0 else xc0
        val otherData = self.datas.getOrElse(other.id, EClassData())
        xycData.uses.addAll(otherData.uses)
        self.datas.remove(other.id)
        self.worklist.add(xyc.id)
        xyc

      override def disunion(xc: EClass, yc: EClass): Unit =
        self.underlying.union(self.Equal(xc, yc), self.False)
        self.underlying.union(self.Equal(yc, xc), self.False)
      override def unequal(xc: EClass, yc: EClass): Boolean =
        self.find(self.Equal(xc, yc)) == self.find(self.False)
      override def hasContradiction: Boolean =
        self.find(self.True) == self.find(self.False)
      private def True: EClass = self.add(EqualityEmbeddingOps.this.True)
      private def False: EClass = self.add(EqualityEmbeddingOps.this.False)
      private def Equal(xc: EClass, yc: EClass): EClass = self.add(EqualityEmbeddingOps.this.Equal(xc, yc))
    }

  /** Basic operations for egraphs with disequality embedding. */
  private trait DisequalityEmbeddingOps extends CommonEGraphOps:
    private val TrueOp: Operator = Operator("@⊤")
    private val UnequalOp: Operator = Operator("@≠")
    private val EmbeddingOps: Set[Operator] = Set(TrueOp, UnequalOp)
    private val True: ENode = ENode(TrueOp)
    private def Unequal(xc: EClass, yc: EClass): ENode = ENode(UnequalOp, Seq(xc, yc))

    private def isEmbedding(x: ENode): Boolean = EmbeddingOps(x.op)

    extension (self: BasicEGraph) {
      override def disunion(xc: EClass, yc: EClass): Unit =
        self.underlying.union(self.Unequal(xc, yc), self.True)
        self.underlying.union(self.Unequal(yc, xc), self.True)
      override def unequal(xc: EClass, yc: EClass): Boolean =
        self.find(self.Unequal(xc, yc)) == self.find(self.True)
      override def hasContradiction: Boolean = self.contradictory
      override def rebuild(): Unit =
        val hasBeenRebuilt: Boolean = self.worklist.nonEmpty
        super.rebuild(self)()
        if hasBeenRebuilt then
          self.contradictory |= self.enodes.exists((x, xcId) =>
            x.op == UnequalOp && self.equal(x.refs(0), x.refs(1)) && // if ne(x, x)
            self.equal(self.classes(xcId), True)                               
          )
      private def True: EClass = self.add(DisequalityEmbeddingOps.this.True)
      private def Unequal(xc: EClass, yc: EClass): EClass = self.add(DisequalityEmbeddingOps.this.Unequal(xc, yc))
    }

// sbt "runMain propel.evaluator.egraph.mutable.X" where X is one of the following mains
@main def testDisequalityEdges(): Unit = testEGraph(using EGraph.DisequalityEdges.EGraphsOps)
@main def testEqualityEmbedding(): Unit = testEGraph(using EGraph.EqualityEmbedding.EGraphsOps)
@main def testDisequalityEmbedding(): Unit = testEGraph(using EGraph.DisequalityEmbedding.EGraphsOps)

def testEGraph(using EGraphOps[EGraph.EGraph]): Unit =
  /** Define your own simple language */
  trait Exp
  case class Fun(fnId: String) extends Exp:
    def apply(args: Exp*): App = App(this, args)
    override def toString: String = fnId
  case class App(fn: Fun, args: Seq[Exp] = Seq()) extends Exp:
    override def toString: String = s"$fn(${args.mkString(",")})"
  
  object SimpleLanguage extends Language[Exp]:
    override def parse(term: Exp)(using EClassGenerator): ENode = term match
      case Fun(fnId) => ENode(Operator(fnId))
      case App(fn, args) => ENode(Operator("apply"), (fn +: args).map(this.parseClass))

  /** Test the egraph implementation on that language */
  val egraph = EGraph()

  import SimpleLanguage.given         // Implicit conversions for using Exps directly, instead of ENodes and EClasses
  given EClassGenerator = egraph.add  // Enable the conversions by providing a way to create EClasses
  import scala.language.implicitConversions

  val (a,b,c,d,e,f,g,h,i) = (Fun("a"), Fun("b"), Fun("c"), Fun("d"), Fun("e"), Fun("f"), Fun("g"), Fun("h"), Fun("i"))
  val fa = egraph.add(f(a))
  val fb = egraph.add(f(b))
  egraph.add(f(a,b,c,d,e,f,g))
  egraph.union(a, b)
  egraph.union(c, d)
  egraph.union(e, f)
  egraph.union(c, b)
  egraph.add(h)

  val egraph2 = EGraph.clone(egraph)
  egraph2.rebuild()

  egraph.disunion(f(a), f(b))
  egraph.rebuild()

  println("\nCANONICALIZATION:")
  println(Seq(a, b, f(a), f(b)).map(e => s"$e: ${egraph.find(e)}").mkString("; "))
  println(s"canonicalize(${f(b)}): ${egraph.canonicalize(f(b))}")
  println(s"canonicalize(${f(b)}): ${egraph2.canonicalize(f(b))}")

  println("\nECLASSES")
  println(s"eclasses: ${egraph.eclasses}")
  println(s"# eclasses: ${egraph.eclasses.size}")
  println(s"# enodes: ${egraph.eclasses.foldLeft(0)(_ + _._2.size)}")
  println(s"eclasses: ${egraph2.eclasses}")
  println(s"# eclasses: ${egraph2.eclasses.size}")
  println(s"# enodes: ${egraph2.eclasses.foldLeft(0)(_ + _._2.size)}")

  println("\nCONTRADICTION:")
  println(s"${f(a)} == ${f(b)}: ${egraph.equal(f(a), f(b))}")
  println(s"${f(a)} != ${f(b)}: ${egraph.unequal(f(a), f(b))}")
  println(s"hasContradiction: ${egraph.hasContradiction}")
  println(s"${f(a)} == ${f(b)}: ${egraph2.equal(f(a), f(b))}")
  println(s"${f(a)} != ${f(b)}: ${egraph2.unequal(f(a), f(b))}")
  println(s"hasContradiction: ${egraph2.hasContradiction}")
