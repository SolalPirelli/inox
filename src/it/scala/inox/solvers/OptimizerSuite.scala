/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class OptimizerSuite extends SolvingTestSuite with DatastructureUtils {
  import trees._
  import dsl._
  import SolverResponses._

  override def configurations =
    for (nme <- Seq(/*"nativez3-opt",*/ "smt-z3-opt")) yield {
      Seq(optSelectedSolvers(Set(nme)))
    }

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head
  }

  val treeId: Identifier = FreshIdentifier("Tree")
  val nodeId: Identifier = FreshIdentifier("Node")
  val emptyId: Identifier = FreshIdentifier("Empty")

  val valueId: Identifier = FreshIdentifier("value")
  val leftId: Identifier = FreshIdentifier("left")
  val rightId: Identifier = FreshIdentifier("right")

  val treeSort = mkSort(treeId)("A") { case Seq(tp) =>
    Seq(
      (nodeId, Seq(ValDef(valueId, IntegerType()), ValDef(leftId, T(treeId)(tp)), ValDef(rightId, T(treeId)(tp)))),
      (emptyId, Seq())
    )
  }

  val sizeId: Identifier = FreshIdentifier("size")

  val sizeFunction = mkFunDef(sizeId)("A") { case Seq(tp) => (
    Seq("t" :: T(treeId)(tp)),
    IntegerType(),
    { case Seq(t) =>
        let("res" :: IntegerType(),
        if_ (t is nodeId) {
          E(BigInt(1)) + E(sizeId)(tp)(t.getField(leftId)) + E(sizeId)(tp)(t.getField(rightId))
        } else_ {
          E(BigInt(0))
        }
      ) (res => Assume(res >= E(BigInt(0)), res))
    }
  )}

  val heightId: Identifier = FreshIdentifier("height")

  val heightFunction = mkFunDef(heightId)("A") { case Seq(tp) => (
    Seq("t" :: T(treeId)(tp)),
    IntegerType(),
    { case Seq(t) =>
      if_ (t is nodeId) {
        E(BigInt(1)) +
        let("res" :: IntegerType(),
          let("leftHeight" :: IntegerType(), E(heightId)(tp)(t.getField(leftId))) (leftHeight => 
            let("rightHeight" :: IntegerType(), E(heightId)(tp)(t.getField(rightId))) (rightHeight => 
              if_ (leftHeight >= rightHeight) { leftHeight }
              else_ { rightHeight  }
            )
          )
        ) (res => Assume(res >= E(BigInt(0)), res))
      } else_ {
        E(BigInt(0))
      }
    }
  )}

  implicit val symbols: inox.trees.Symbols = {
    NoSymbols
      .withFunctions(Seq(sizeFunction, heightFunction))
      .withSorts(Seq(treeSort))
  }

  val program = inox.Program(inox.trees)(symbols)

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

  test("n times n") { implicit ctx =>
    val x = Variable.fresh("x", Int32Type())
    val prop = GreaterEquals(Times(x, x), Int32Literal(10))

    val factory = SolverFactory.optimizer(program, ctx)
    val optimizer = factory.getNewSolver()
    try {
      optimizer.assertCnstr(Not(prop))
      optimizer.minimize(x)
      optimizer.check(Model) match {
        case SatWithModel(model) =>
          println(model)
          model.vars.get(x.toVal).get match {
            case Int32Literal(c) => assert(c == 0)
          }
        case _ =>
          fail("Expected sat-with-model")
      }
    } finally {
      factory.reclaim(optimizer)
    }
  }

  test("binary trees") { implicit ctx =>
    val aTree = Variable.fresh("aTree", T(treeId)(IntegerType()))
    val clause = Equals(E(heightId)(IntegerType())(aTree), IntegerLiteral(BigInt(3)))

    val factory = SolverFactory.optimizer(program, ctx)
    val optimizer = factory.getNewSolver()
    try {
      optimizer.assertCnstr(clause)
      optimizer.minimize(E(sizeId)(IntegerType())(aTree))
      optimizer.check(Model) match {
        case SatWithModel(model) =>
          println(model)
        case _ =>
          fail("Expected sat-with-model")
      }
    } finally {
      factory.reclaim(optimizer)
    }
  }
}
