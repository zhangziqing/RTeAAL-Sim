package essent

import essent.TeAALExtractor.{BufferHashMap, opInOrder}
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

/** Shared, explicitly sized expression DAG. References are immutable cycle inputs
  * or existing tensor values; numeric tensor operands are unsigned bit patterns.
  */
object SliceGraph {
  def mask(width: Int): BigInt = (BigInt(1) << width) - 1
  private val util = new TeAALUtil
  def number(s: String): Option[BigInt] =
    if (s.matches("-?[0-9]+") || util.isInte(s))
      scala.util.Try(util.stringInt(s)).toOption else None
  case class Expr(kind: String, args: Vector[Int], width: Int,
                  signal: String = "", lo: Int = 0, value: BigInt = 0)
  class Pool {
    val nodes = ArrayBuffer.empty[Expr]
    private val interned = HashMap.empty[Expr, Int]
    def apply(id: Int): Expr = nodes(id)
    def intern(e: Expr): Int = interned.getOrElseUpdate(e, { nodes += e; nodes.size - 1 })
    def const(value: BigInt, width: Int): Int = intern(Expr("const", Vector.empty, width, value = value & mask(width)))
    def ref(signal: String, lo: Int, width: Int): Int = number(signal) match {
      case Some(v) => const(v >> lo, width)
      case None => intern(Expr("ref", Vector.empty, width, signal, lo))
    }
    def op(kind: String, args: Vector[Int], width: Int): Int = {
      val es = args.map(apply)
      def lit(i: Int, v: BigInt): Boolean = es(i).kind == "const" && es(i).value == v
      kind match {
        case "mux" if args(1) == args(2) => args(1)
        case "mux" if lit(0, 0) => args(2)
        case "mux" if lit(0, 1) => args(1)
        case "and" if lit(0, 0) || lit(1, 0) => const(0, width)
        case "and" if lit(0, mask(width)) => args(1)
        case "and" if lit(1, mask(width)) => args(0)
        case "or" | "xor" if lit(0, 0) => args(1)
        case "or" | "xor" if lit(1, 0) => args(0)
        case "and" | "or" if args(0) == args(1) => args(0)
        case "xor" if args(0) == args(1) => const(0, width)
        case "mux" if lit(1, 1) && lit(2, 0) && width == 1 => args(0)
        case "mux" if lit(1, 0) && lit(2, 1) && width == 1 => op("xor", Vector(args(0), const(1, 1)), 1)
        case _ if es.forall(_.kind == "const") && Set("and", "or", "xor", "catn")(kind) =>
          val vs = es.map(_.value)
          val v = kind match {
            case "and" => vs(0) & vs(1)
            case "or" => vs(0) | vs(1)
            case "xor" => vs(0) ^ vs(1)
            case "catn" => es.foldLeft(BigInt(0))((v, e) => (v << e.width) | e.value)
          }
          const(v, width)
        case "catn" if args.size == 1 => args.head
        case "catn" =>
          def binary(start: Int, end: Int): Int = {
            if (end - start == 1) args(start)
            else {
              val mid = start + (end - start) / 2
              val a = binary(start, mid); val b = binary(mid, end)
              op("cat", Vector(a, b), apply(a).width + apply(b).width)
            }
          }
          require(args.nonEmpty && es.map(_.width).sum == width)
          binary(0, args.size)
        case _ => intern(Expr(kind, args, width))
      }
    }
    def reachable(root: Int): Vector[Int] = {
      val seen = HashSet.empty[Int]
      val stack = ArrayBuffer(root)
      while (stack.nonEmpty) {
        val id = stack.remove(stack.size - 1)
        if (seen.add(id)) stack ++= apply(id).args
      }
      seen.toVector.sorted
    }
    def references(root: Int): Set[String] = reachable(root).iterator.map(apply)
      .filter(_.kind == "ref").map(_.signal).toSet
  }

  class Graph(val ops: opInOrder, val users: BufferHashMap, val producers: BufferHashMap,
              val outputs: HashMap[String, String], val widths: HashMap[String, Int],
              val protectedNames: Set[String] = Set.empty, val states: Set[String] = Set.empty) {
    val liveUsers = HashMap.empty[String, HashSet[String]]
    ops.foreach { case (op, ins) => ins.keysIterator.filter(s => number(s).isEmpty).foreach { s =>
      liveUsers.getOrElseUpdate(s, HashSet.empty) += op
    }}
    val aliases = HashMap.empty[String, HashSet[String]]
    producers.foreach { case (s, ps) => ps.foreach(p => aliases.getOrElseUpdate(p, HashSet.empty) += s) }
    def kind(op: String): String = op.takeWhile(_ != '_')
    def ordered(op: String): Vector[String] = {
      val pairs = ops(op).toVector.flatMap { case (s, ps) => ps.toVector.map(_ -> s) }
      if (pairs.isEmpty || pairs.map(_._1).sorted != pairs.indices.toVector) Vector.empty
      else pairs.sortBy(_._1).map(_._2)
    }
    def producer(s: String): Option[String] =
      if (states(s)) None else producers.get(s).filter(_.size == 1).flatMap(_.headOption).filter(ops.contains)
    def width(s: String): Int = widths.getOrElse(s, 0)
    // Width metadata does not prove that a narrow host slot is normalized.
    // Only the actual producer semantics can justify omitting truncation.
    def canReuseReference(e: Expr): Boolean = e.kind == "ref" &&
      e.lo == 0 && e.width >= 1 && e.width <= 64 && normalized(e.signal, e.width)
    private def normalized(signal: String, bits: Int): Boolean = {
      // Keep the proof local to this graph version and bound its traversal.
      // State leaves, arithmetic, memory and out-of-band lookups stay opaque.
      val memo = HashMap.empty[(String, Int), Boolean]
      var visits = 0
      def prove(s: String, w: Int, level: Int): Boolean = {
        if (w == 64) return true
        if (w < 1 || w > 64 || level >= 32 || visits >= 128) return false
        memo.getOrElseUpdate(s -> w, {
          visits += 1
          number(s) match {
            case Some(v) => v >= 0 && v <= mask(w)
            case None => producer(s).exists { op =>
              val in = ordered(op)
              def bounded(i: Int, n: Int = w): Boolean = prove(in(i), n, level + 1)
              kind(op) match {
                case "lt" | "ltS" | "leq" | "leqS" | "eq" | "neq" => in.size == 2
                case "xorr" => in.size == 1
                case "and" => in.size == 2 && (bounded(0) || bounded(1))
                case "or" | "xor" => in.size == 2 && bounded(0) && bounded(1)
                case "assign" => in.size == 1 && bounded(0)
                case "mux" => in.size == 3 && bounded(1) && bounded(2)
                case "bits" => in.size == 3 &&
                  number(in(1)).exists(n => n >= 0 && n < 64) && bounded(2)
                case "cat" => in.size == 3 && number(in(2)).exists { shift =>
                  shift > 0 && shift < w && bounded(0, w - shift.toInt) && bounded(1, shift.toInt)
                }
                case _ => false
              }
            }
          }
        })
      }
      prove(signal, bits, 0)
    }
    def removable(op: String): Boolean = !protectedNames(op) &&
      !aliases.getOrElse(op, HashSet.empty).exists(s => protectedNames(s) || states(s)) &&
      aliases.getOrElse(op, HashSet.empty).size == 1 &&
      !Set("memr", "memw", "lookup", "chain")(kind(op))
    private val depths = HashMap.empty[String, Int]
    def depth(s: String): Int = {
      val pending = ArrayBuffer(s -> false)
      val visiting = HashSet.empty[String]
      while (pending.nonEmpty) {
        val (name, ready) = pending.remove(pending.size - 1)
        if (!depths.contains(name)) producer(name) match {
          case None => depths(name) = 0
          case Some(op) if ready =>
            depths(name) = 1 + ops(op).keysIterator.map(n => depths.getOrElse(n, 0)).maxOption.getOrElse(0)
            visiting -= name
          case Some(op) =>
            require(visiting.add(name), s"Cycle in projection input at $name")
            pending += name -> true
            pending ++= ops(op).keysIterator.filterNot(depths.contains).map(_ -> false)
        }
      }
      depths(s)
    }
    def expressionDepth(pool: Pool, root: Int): Int = {
      val ds = HashMap.empty[Int, Int]
      pool.reachable(root).foreach { id =>
        val e = pool(id)
        ds(id) = e.kind match {
          case "const" => 0
          case "ref" => depth(e.signal) + (if (canReuseReference(e)) 0 else 1)
          case "catn" =>
            def tree(start: Int, end: Int): Int = {
              if (end - start == 1) ds(e.args(start))
              else { val mid = start + (end - start) / 2; 1 + tree(start, mid).max(tree(mid, end)) }
            }
            tree(0, e.args.size)
          case _ => 1 + e.args.map(ds).maxOption.getOrElse(0)
        }
      }
      ds(root)
    }
    def invalidateDepths(changed: Set[String]): Unit = {
      val work = ArrayBuffer.from(changed)
      val seen = HashSet.empty[String]
      while (work.nonEmpty) {
        val s = work.remove(work.size - 1)
        if (seen.add(s)) {
          depths.remove(s)
          liveUsers.getOrElse(s, HashSet.empty).foreach(op => outputs.get(op).foreach(work += _))
        }
      }
    }
  }
}
