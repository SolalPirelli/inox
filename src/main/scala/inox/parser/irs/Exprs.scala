package inox
package parser
package irs

trait Exprs { self: IRs =>

  object Exprs {
    sealed abstract class Quantifier
    case object Forall extends Quantifier
    case object Lambda extends Quantifier

    object Unary {
      sealed abstract class Operator
      case object Minus extends Operator
      case object Not extends Operator
      case object BVNot extends Operator
      case object StringLength extends Operator
    }

    object Binary {
      sealed abstract class Operator
      case object Plus extends Operator
      case object Minus extends Operator
      case object Times extends Operator
      case object Division extends Operator
      case object Modulo extends Operator
      case object Remainder extends Operator
      case object Implies extends Operator
      case object Equals extends Operator
      case object LessEquals extends Operator
      case object LessThan extends Operator
      case object GreaterEquals extends Operator
      case object GreaterThan extends Operator
      case object BVAnd extends Operator
      case object BVOr extends Operator
      case object BVXor extends Operator
      case object BVShiftLeft extends Operator
      case object BVAShiftRight extends Operator
      case object BVLShiftRight extends Operator
      case object SetAdd extends Operator
      case object ElementOfSet extends Operator
      case object SetIntersection extends Operator
      case object SetUnion extends Operator
      case object SetDifference extends Operator
      case object BagAdd extends Operator
      case object MultiplicityInBag extends Operator
      case object BagIntersection extends Operator
      case object BagUnion extends Operator
      case object BagDifference extends Operator
      case object MapApply extends Operator
      case object StringConcat extends Operator
    }

    object Ternary {
      sealed abstract class Operator
      case object SubString extends Operator
      case object MapUpdated extends Operator
    }

    object NAry {
      sealed abstract class Operator
      case object And extends Operator
      case object Or extends Operator
    }

    object Casts {
      sealed abstract class Mode
      case object Widen extends Mode
      case object Narrow extends Mode
    }

    sealed trait Expr extends IR {
      override def getHoles: Seq[Hole] = this match {
        case ExprHole(index) => Seq(Hole(index, HoleTypes.Expr))
        case SetConstruction(elems) => elems.getHoles
        case BagConstruction(elems) => elems.getHoles
        case MapConstruction(elems, default) => elems.getHoles ++ default.getHoles
        case Variable(id) => id.getHoles
        case UnaryOperation(_, expr) => expr.getHoles
        case BinaryOperation(_, lhs, rhs) => lhs.getHoles ++ rhs.getHoles
        case Invocation(id, typeArgs, args) => id.getHoles ++ typeArgs.getHoles ++ args.getHoles
        case Application(callee, args) => callee.getHoles ++ args.getHoles
        case Abstraction(_, bindings, body) => bindings.getHoles ++ body.getHoles
        case Let(binding, value, body) => binding.getHoles ++ value.getHoles ++ body.getHoles
        case If(condition, thenn, elze) => condition.getHoles ++ thenn.getHoles ++ elze.getHoles
        case Selection(structure, id) => structure.getHoles ++ id.getHoles
        case TypeAnnotation(expr, tpe) => expr.getHoles ++ tpe.getHoles
        case Choose(binding, body) => binding.getHoles ++ body.getHoles
        case Assume(pred, body) => pred.getHoles ++ body.getHoles
        case _ => Seq()
      }
    }

    case class ExprHole(index: Int) extends Expr
    case class UnitLiteral() extends Expr
    case class BooleanLiteral(value: Boolean) extends Expr
    case class IntegerLiteral(value: BigInt) extends Expr
    case class FractionLiteral(numerator: BigInt, denominator: BigInt) extends Expr
    case class StringLiteral(value: String) extends Expr
    case class CharLiteral(value: Char) extends Expr
    case class SetConstruction(elems: ExprSeq) extends Expr
    case class BagConstruction(elems: ExprPairSeq) extends Expr
    case class MapConstruction(elems: ExprPairSeq, default: Expr) extends Expr
    case class Variable(id: Identifiers.Identifier) extends Expr
    case class UnaryOperation(operator: Unary.Operator, expr: Expr) extends Expr
    case class BinaryOperation(operator: Binary.Operator, lhs: Expr, rhs: Expr) extends Expr
    case class TernaryOperation(operator: Ternary.Operator, lhs: Expr, mid: Expr, rhs: Expr) extends Expr
    case class Operation(operator: NAry.Operator, args: ExprSeq) extends Expr
    case class Invocation(id: Identifiers.Identifier, typeArgs: Types.TypeSeq, args: ExprSeq) extends Expr
    case class Application(callee: Expr, args: ExprSeq) extends Expr
    case class Abstraction(quantifier: Quantifier, bindings: Bindings.BindingSeq, body: Expr) extends Expr
    case class Let(binding: Bindings.Binding, value: Expr, body: Expr) extends Expr
    case class If(condition: Expr, thenn: Expr, elze: Expr) extends Expr
    case class Selection(structure: Expr, id: Identifiers.Identifier) extends Expr
    case class TupleSelection(tuple: Expr, index: Int) extends Expr
    case class TypeAnnotation(expr: Expr, tpe: Types.Type) extends Expr
    case class Choose(binding: Bindings.Binding, body: Expr) extends Expr
    case class Assume(pred: Expr, body: Expr) extends Expr
    case class IsConstructor(expr: Expr, constructor: Identifiers.Identifier) extends Expr
    case class Cast(mode: Casts.Mode, expr: Expr, target: Int) extends Expr

    implicit object holeTypableExpr extends HoleTypable[Expr] {
      override val holeType = HoleTypes.Expr
    }

    type ExprSeq = HSeq[Expr]

    sealed abstract class ExprPair extends IR {
      override def getHoles: Seq[Hole] = this match {
        case Pair(lhs, rhs) => lhs.getHoles ++ rhs.getHoles
        case PairHole(index) => Seq(Hole(index, HoleTypes.Pair(HoleTypes.Expr, HoleTypes.Expr)))
      }
    }

    case class Pair(lhs: Expr, rhs: Expr) extends ExprPair
    case class PairHole(index: Int) extends ExprPair

    implicit object holeTypableExprPair extends HoleTypable[ExprPair] {
      override val holeType = HoleTypes.Pair(HoleTypes.Expr, HoleTypes.Expr)
    }

    type ExprPairSeq = HSeq[ExprPair]
  }
}