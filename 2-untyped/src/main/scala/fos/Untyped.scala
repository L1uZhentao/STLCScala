package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  untyped lambda calculus found in Chapter 5 of
 *  the TAPL book.
 */
object Untyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".")
  import lexical.Identifier

  /** t ::= x
          | '\' x '.' t
          | t t
          | '(' t ')'
   */
  def term: Parser[Term] = 
    single_term ~ rep(single_term) ^^ {
      case t0 ~ ts => ts.foldLeft(t0){(m, n) => App(m, n)}
    }

  def single_term: Parser[Term] = 
      (ident ^^ (x => Var(x)))
    | "\\" ~ ident ~ "." ~ term ^^ {case _ ~ name ~ _ ~ t => Abs(name, t)}
    | "(" ~ term ~ ")" ^^ { case _ ~ t ~ _ => t }

  /** <p>
   *    Alpha conversion: term <code>t</code> should be a lambda abstraction
   *    <code>\x. t</code>.
   *  </p>
   *  <p>
   *    All free occurences of <code>x</code> inside term <code>t/code>
   *    will be renamed to a unique name.
   *  </p>
   *
   *  @param t the given lambda abstraction.
   *  @return  the transformed term with bound variables renamed.
   */
  def alpha(t: Abs): Abs = t match 
    case Abs(x, t1) => 
      val idString = incr().toString()
      Abs(idString, renameWithId(t1, x, idString)) 
    case _ => t

  var id : Long = 0
  def incr(): Long = {
    id += 1
    id
  }

  def renameWithId(t: Term, x: String, labelid: String) : Term = t match
    case Var(y) if y == x => Var(labelid)
    case Var(y) if y != x => t
    case Abs(y, t1) if y == x => Abs(labelid, renameWithId(t1, x, labelid))
    case Abs(y, t1) if y != x => Abs(y, renameWithId(t1, x, labelid))
    case App(t1, t2) => App(renameWithId(t1, x, labelid), renameWithId(t2, x, labelid))
    case _ => t

  def FV(t: Term): List[String] = 
    def FV_helper(t: Term, fv_list: List[String]): List[String] = t match
      case Var(x) => x :: fv_list
      case Abs(x, t1) => FV_helper(t1, fv_list).filter(y => y != x)
      case App(t1, t2) => fv_list ++ FV_helper(t1, List()) ++ FV_helper(t2, List())
    FV_helper(t, List())
      
  

  /** Straight forward substitution method
   *  (see definition 5.3.5 in TAPL book).
   *  [x -> s]t
   *
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  ...
   */
  def subst(t: Term, x: String, s: Term): Term = t match 
      case Var(y) if y == x => s
      case Var(y) if y != x => t
      case Abs(y, t1) if y == x => t
      case Abs(y, t1) if y != x && ! FV(s).contains(y) => Abs(y, subst(t1, x, s))
      case Abs(y, t1) if y != x && FV(s).contains(y) => subst(alpha(Abs(y, t1)), x, s)
      case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
      case _ => t


  /** Term 't' does not match any reduction rule. */
  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Normal order (leftmost, outermost redex first).
   *
   *  @param t the initial term
   *  @return  the reduced term
   */
  def reduceNormalOrder(t: Term): Term = t match 
    // For the forth rule: App + Abs
    case App(Abs(x, y), z) => subst(y, x, z)
    // For first two rules: App
    // The leftmost/ outmost should be reduced first
    case App(x, y) => (x, y) match 
      case (Var(xv), Var(yv)) => throw NoReductionPossible(t)
      case (Var(xv), _) => App(x, reduceNormalOrder(y))
      case (_, Var(yv)) => App(reduceNormalOrder(x), y)
      case _ => 
        try 
          App(reduceNormalOrder(x), y)
        catch 
          case e: NoReductionPossible => App(x, reduceNormalOrder(y))
    // For the third rule: Abs
    case Abs(x, y) => Abs(x, reduceNormalOrder(y))
    case _ => throw NoReductionPossible(t)

  /** Call by value reducer. */
  def reduceCallByValue(t: Term): Term =  t match 
    // For the forth rule: App + Abs
    case App(Abs(x, y), z) if z.isInstanceOf[Abs] => subst(y, x, z)
    // For first three rules: App
    case App(x, y) => x match 
      case App(_, _) => App(reduceCallByValue(x), y)
      case Abs(_, _) if y.isInstanceOf[App] => App(x, reduceCallByValue(y))
      case _ => throw NoReductionPossible(t)
    case _ => throw NoReductionPossible(t)
  


  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the method that reduces a term by one step.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): LazyList[Term] =
    try {
      var t1 = reduce(t)
      LazyList.cons(t, path(t1, reduce))
    } catch {
      case NoReductionPossible(_) =>
        LazyList.cons(t, LazyList.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        println("normal order: ")
        for (t <- path(trees, reduceNormalOrder))
          println(t)
        println("call-by-value: ")
        for (t <- path(trees, reduceCallByValue))
          println(t)

      case e =>
        println(e)
    }
  }
}
