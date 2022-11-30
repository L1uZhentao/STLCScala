package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the NB
 *  language of booleans and numbers found in Chapter 3 of
 *  the TAPL book.
 */
object Arithmetic extends StandardTokenParsers {
  lexical.reserved ++= List("true", "false", "if", "then", "else", "succ", "pred", "iszero")

  import lexical.NumericLit

  
  /** Pasre numericLit */

  def parseNumeric(n : Int) : Term = 
    if n == 0 then Zero
    // According to the rule, we do not consider the negative case: else if n < 0 then Pred(parseNumeric(n + 1) )
    else Succ(parseNumeric(n - 1) )
  
  /** term ::= 'true'
             | 'false'
             | 'if' term 'then' term 'else' term
             | numericLit
             | 'succ' term
             | 'pred' term
             | 'iszero' term
   */

  def term: Parser[Term] = (
      // note: you should use `numericLit` to parse numeric literals
      "true" ^^^ True |
      "false" ^^^ False |
      ("if" ~ term ~ "then" ~ term ~ "else" ~ term) ^^ {
          case _ ~ c1 ~ _ ~ c2 ~ _ ~ c3 => If(c1, c2, c3)
      } |
      numericLit ^^ {case num => parseNumeric(num.toInt)} |
      ("succ" ~ term) ^^ {case _ ~ t => Succ(t)} |
      ("pred" ~ term) ^^ {case _ ~ t => Pred(t)}  |
      ("iszero" ~ term) ^^ {case _ ~ t => IsZero(t)} 
  )


  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Return a list of at most n terms, each being one step of reduction. */
  def path(t: Term, n: Int = 64): List[Term] =
    if (n <= 0) Nil
    else
      t :: {
        try {
          path(reduce(t), n - 1)
        } catch {
          case NoReductionPossible(t1) =>
            Nil
        }
      }

 /** To check if it a reducible numeric */
  def isReducibleNumeric(t : Term) : Boolean = t match
    case Zero => true 
    case Pred(v) => isReducibleNumeric(v)
    case Succ(v) => isReducibleNumeric(v)
    case If(cond, t1, t2) => eval(cond) match 
        case True => isNumeric(t1)
        case False => isNumeric(t2)
        case _ => false
    case _ => false // throw new TermIsStuck(t) if this case, the exception would be wrong


  /** To check if it a numeric */
  def isNumeric(t : Term) : Boolean = t match
    case Zero => true 
    case Pred(v) => isNumeric(v)
    case Succ(v) => isNumeric(v)
    case If(cond, t1, t2) => eval(cond) match 
        case True => isNumeric(t1)
        case False => isNumeric(t2)
        case _ => false
    case _ => false // throw new TermIsStuck(t) if this case, the exception would be wrong

  /** Perform one step of reduction, when possible.
   *  If reduction is not possible NoReductionPossible exception
   *  with corresponding irreducible term should be thrown.
   */
  def reduce(t: Term): Term = t match 
    // TODO: double check all cases
    // 0928 31/35
    // 0928 last attempt 34/35
    case If(cond, t1, t2) => cond match
      case True => t1
      case False => t2 
      case _ => If(reduce(cond), t1, t2)
    case IsZero(v) => v match
      case Zero => True
      case Succ(m) => 
        if isNumeric(m) then False
        else throw new NoReductionPossible(v)
      case _ => IsZero(reduce(v))
    case Pred(v) => v match
      case Zero => Zero
      case Succ(m) =>
        if isNumeric(m) then m 
        else throw new NoReductionPossible(v)
      case _ => Pred(reduce(v))
    case Succ(v) => Succ(reduce(v))
    case _ => throw new NoReductionPossible(t)

  case class TermIsStuck(t: Term) extends Exception(t.toString)

  /** Perform big step evaluation (result is always a value.)
   *  If evaluation is not possible TermIsStuck exception with
   *  corresponding inner irreducible term should be thrown.
   */
  def eval(t: Term): Term = t match 
    // TODO: double check all cases
    case If(cond, t1, t2) => eval(cond) match
      case True => eval(t1)//0928 t1
      case False => eval(t2) //0928 t2
      case _ => throw new TermIsStuck(t)
    case IsZero(m) => eval(m) match
      case Zero => True
      case Succ(v) if isNumeric(v) => False
      case _ => throw new TermIsStuck(t)
    case Pred(m) => eval(m) match
      case Zero => Zero
      case Succ(v) if isNumeric(v) => v
      case _ => throw new TermIsStuck(t)
    case Succ(m) => eval(m) match
      case v if isNumeric(v) => Succ(v)
      case _ => throw new TermIsStuck(t)
    case True | False | Zero => t
    case _ => throw new TermIsStuck(t)

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    print(phrase(term)(tokens))
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        for (t <- path(trees))
          println(t)
        try {
          print("Big step: ")
          println(eval(trees))
        } catch {
          case TermIsStuck(t) => println("Stuck term: " + t)
        }
      case e =>
        println(e)
    }
  }
}
