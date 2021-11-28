/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class OptimizerSuite extends SolvingTestSuite with DatastructureUtils {
  import trees._
  import dsl._
  import SolverResponses._

  override def configurations =
    for (nme <- Seq("nativez3-opt", "smt-z3-opt")) yield {
      Seq(optSelectedSolvers(Set(nme)))
    }

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head
  }

  val program = inox.Program(inox.trees)(NoSymbols)

  def getIntegerValue(model: program.Model, v: Variable): BigInt = model.vars.get(v.toVal).get match {
    case IntegerLiteral(n) => n
  }

  test("unsatisfiable soft constraint") { implicit ctx =>
    val v = Variable.fresh("x", IntegerType())
    val clause = GreaterThan(v, IntegerLiteral(BigInt(10)))
    val softClause = GreaterThan(IntegerLiteral(BigInt(10)), v)

    val factory = SolverFactory.optimizer(program, ctx)
    val optimizer = factory.getNewSolver()
    try {
      optimizer.assertCnstr(clause)
      optimizer.assertCnstr(softClause, 1)
      optimizer.check(Model) match {
        case SatWithModel(model) =>
          assert(getIntegerValue(model, v) > 10)
        case _ =>
          fail("Expected sat-with-model")
      }
    } finally {
      factory.reclaim(optimizer)
    }
  }

  test("one satisfiable soft constraint out of two") { implicit ctx =>
    val v = Variable.fresh("x", IntegerType())
    val softClause1 = GreaterThan(v, IntegerLiteral(BigInt(10)))
    val softClause2 = GreaterThan(IntegerLiteral(BigInt(-10)), v)

    val factory = SolverFactory.optimizer(program, ctx)
    val optimizer = factory.getNewSolver()
    try {
      optimizer.assertCnstr(softClause1, 1)
      optimizer.assertCnstr(softClause2, 2)
      optimizer.check(Model) match {
        case SatWithModel(model) =>
          assert(getIntegerValue(model, v) < -10)
        case _ =>
          fail("Expected sat-with-model")
      }
    } finally {
      factory.reclaim(optimizer)
    }
  }
}
