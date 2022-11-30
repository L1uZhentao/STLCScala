package fos

import scala.util.parsing.input.Positional

/** Abstract Syntax Trees for terms. */
sealed abstract class Term extends Positional

case object True extends Term {
  override def toString() = "true"
}
case object False extends Term {
  override def toString() = "false"
}
case object Zero extends Term {
  override def toString() = "0"
}
case class Succ(t: Term) extends Term {
  override def toString() = s"(succ $t)"
}
case class Pred(t: Term) extends Term {
  override def toString() = s"(pred $t)"
}
case class IsZero(t: Term) extends Term {
  override def toString() = s"(iszero $t)"
}
case class If(cond: Term, t1: Term, t2: Term) extends Term {
  override def toString() = s"if $cond then $t1 else $t2"
}

case class Var(name: String) extends Term {
  override def toString() = name
}
case class Abs(v: String, tp: Type, t: Term) extends Term {
  override def toString() = s"(\\$v: $tp. $t)"
}
case class App(t1: Term, t2: Term) extends Term {
  override def toString() = s"($t1 $t2)"
}
case class TermPair(t1: Term, t2: Term) extends Term {
  override def toString() = s"{ $t1, $t2 }"
}

case class First(t: Term) extends Term {
  override def toString() = s"(fst $t)"
}

case class Second(t: Term) extends Term {
  override def toString() = s"(snd $t)"
}

case class Inl(t: Term, tpe: Type) extends Term {
  override def toString() = s"(inl $t as $tpe)"
}

case class Inr(t: Term, tpe: Type) extends Term {
  override def toString() = s"(inr $t as $tpe)"
}

case class Case(t: Term, x1: String, t1: Term, x2: String, t2: Term) extends Term {
  override def toString() = s"(case $t of inl $x1 => $t1 | inr $x2 => $t2)"
}

case class Fix(t: Term) extends Term {
  override def toString() = s"(fix $t)"
}

// Imperative bundle

case object UnitVal extends Term

case class Sequence(t1: Term, t2: Term) extends Term

case class Ref(t1: Term) extends Term

case class Deref(t1: Term) extends Term

case class Assign(t1: Term, t2: Term) extends Term

case class Loc(location: Location) extends Term

// Functional bundle

case class TypeAbs(x: String, t2: Term) extends Term

case class TypeApp(t1: Term, tp: Type) extends Term

case class NilVal(tp: Type) extends Term

case class Cons(tp: Type, t1: Term, t2: Term) extends Term

case class ListCase(t1: Term, t2: Term, x: String, y: String, t3: Term)

// Function/subtyping bundle

case class Record(fields: List[(String, Term)]) extends Term

case class RecordProj(t1: Term, l: String) extends Term

// Subtyping bundle

case class Ascription(t: Term, tp: Type) extends Term

/** Abstract Syntax Trees for types. */
abstract class Type extends Positional

case object TypeBool extends Type {
  override def toString() = "Bool"
}
case object TypeNat extends Type {
  override def toString() = "Nat"
}
case class TypeFun(t1: Type, t2: Type) extends Type {
  override def toString() = s"($t1 -> $t2)"
}
case class TypePair(t1: Type, t2: Type) extends Type {
  override def toString() = s"($t1 * $t2)"
}
case class TypeSum(t1: Type, t2: Type) extends Type {
  override def toString() = s"($t1 + $t2)"
}

// Imperative bundle

case object TypeUnit extends Type

case class TypeRef(t1: Type) extends Type

/** Location in the store */
final class Location private ()

object Location {
  def fresh(): Location = new Location()
}

/** Store */
final class Store private (underlying: Map[Location, Term]) {
  def get(location: Location): Option[Term] = underlying.get(location)

  def addOrReplace(location: Location, value: Term): Store =
    new Store(underlying + (location -> value))
}

object Store {
  def empty: Store = new Store(Map.empty)
}

// Functional bundle

case class TypeVar(name: String) extends Type

case class TypeUniversal(x: TypeVar, t1: Type) extends Type

case class TypeList(t1: Type) extends Type

// Function/subtyping bundle

case class TypeRecord(fieldTypes: List[(String, Type)]) extends Type
