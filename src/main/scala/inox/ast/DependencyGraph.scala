/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import utils.Lazy
import utils.Graphs._

trait DependencyGraph extends CallGraph {
  import trees._

  protected class SortCollector extends Collector {
    override def traverse(tpe: Type): Unit = tpe match {
      case ADTType(id, _) =>
        register(id)
        super.traverse(tpe)
      case _ =>
        super.traverse(tpe)
    }

    override def traverse(expr: Expr): Unit = expr match {
      case ADT(id, _, _) =>
        register(symbols.getConstructor(id).sort)
        super.traverse(expr)
      case _ =>
        super.traverse(expr)
    }
  }

  protected def getSortCollector: SortCollector = new SortCollector

  private def collectSorts(fd: FunDef): Set[Identifier] = {
    val collector = getSortCollector
    collector.traverse(fd)
    collector.result
  }

  private def collectSorts(sort: ADTSort): Set[Identifier] = {
    val collector = getSortCollector
    collector.traverse(sort)
    collector.result
  }

  protected def computeDependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = callGraph
    for ((_, fd) <- symbols.functions; id <- collectSorts(fd)) {
      g += SimpleEdge(fd.id, id)
    }
    for ((_, sort) <- symbols.sorts; id <- collectSorts(sort)) {
      g += SimpleEdge(sort.id, id)
    }
    g
  }

  @inline def dependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = _dependencyGraph.get
  private[this] val _dependencyGraph: Lazy[DiGraph[Identifier, SimpleEdge[Identifier]]] = Lazy(computeDependencyGraph)

  def dependsOn(from: Identifier, to: Identifier): Boolean = {
    dependencyGraph.transitiveSucc(from) contains to
  }

  def dependencies(from: Identifier): Set[Identifier] = {
    dependencyGraph.transitiveSucc(from)
  }
}
