package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd")

  /** t ::=          "true"
   *               | "false"
   *               | number
   *               | "succ" t
   *               | "pred" t
   *               | "iszero" t
   *               | "if" t "then" t "else" t
   *               | ident
   *               | "\" ident ":" T "." t
   *               | t t
   *               | "(" t ")"
   *               | "let" ident ":" T "=" t "in" t
   *               | "{" t "," t "}"
   *               | "fst" t
   *               | "snd" t
   */


  def parseNumeric(n : Int) : Term = 
    if n == 0 then Zero
    else Succ(parseNumeric(n - 1) )
  

  def simple_parse_type: Parser[Type] = 
      "Bool" ^^^ TypeBool
    | "Nat" ^^^ TypeNat
    | "(" ~ parse_type ~ ")" ^^ { case _ ~ t ~ _ => t}

  def pair_parse_type: Parser[Type] = repsep(simple_parse_type, "*") ^^ {
    case tseq => tseq.reduceRight((t1, t2) => TypePair(t1, t2))
  }

  def parse_type: Parser[Type] = repsep(pair_parse_type, "->") ^^ {
    case tseq => tseq.reduceRight((t1, t2) => TypeFun(t1, t2))
  }

  def term: Parser[Term] = 
    single_term ~ rep(single_term) ^^ {
      case t0 ~ ts => ts.foldLeft(t0){(m, n) => App(m, n)}
    }

  def single_term: Parser[Term] = 
    // Syntex for Boolean and Numeric Values
    "true" ^^^ True |
    "false" ^^^ False |
    ("if" ~ term ~ "then" ~ term ~ "else" ~ term) ^^ {
        case _ ~ c1 ~ _ ~ c2 ~ _ ~ c3 => If(c1, c2, c3)
    } |
    numericLit ^^ {case num => parseNumeric(num.toInt)} |
    ("succ" ~ term) ^^ {case _ ~ t => Succ(t)} |
    ("pred" ~ term) ^^ {case _ ~ t => Pred(t)}  |
    ("iszero" ~ term) ^^ {case _ ~ t => IsZero(t)} | 
    // The following is for lambda calculus
    ident ^^ {case s => Var(s)} | 
    "\\" ~ ident ~ ":" ~ parse_type ~ "." ~ term ^^ {case _ ~ x ~ _ ~ ty ~ _ ~ t => Abs(x, ty, t)} |
    "(" ~ term ~ ")" ^^ { case _ ~ t ~ _ => t } |
    // The following is for pairs
    "fst" ~ term ^^ {case _ ~ t1 => First(t1)} | 
    "snd" ~ term ^^ {case _ ~ t1 => Second(t1)} |
    "{" ~ term ~ "," ~ term ~ "}" ^^ { case _ ~ t1 ~ _ ~ t2 ~ _ => TermPair(t1,t2)} |
    // The following is for let
    "let" ~ ident ~ ":" ~ parse_type ~ "=" ~ term ~ "in" ~ term ^^ {
      case _ ~ x ~ _ ~ ty ~ _ ~ t1 ~ _ ~ t2 =>
          App(Abs(x, ty, t2), t1)
    }


  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]


  def alpha(t: Abs): Abs = t match 
    case Abs(x, ty, t1) => 
      val idString = incr().toString()
      Abs(idString, ty, renameWithId(t1, x, idString)) 
    case _ => t

  var id : Long = 0
  def incr(): Long = {
    id += 1
    id
  }

  def renameWithId(t: Term, x: String, labelid: String) : Term = t match
    // These are for boolean and numeric
    case IsZero(t0)  => IsZero(renameWithId(t0, x, labelid))
    case Succ(t0)  => Succ(renameWithId(t0, x, labelid))
    case Pred(t0)  => Pred(renameWithId(t0, x, labelid))
    // These are for Pair
    case First(t0) => First(renameWithId(t0, x, labelid))
    case Second(t0) => Second(renameWithId(t0, x, labelid))
    case TermPair(t1, t2) => TermPair(renameWithId(t1, x, labelid), renameWithId(t2, x, labelid))
    // For if 
    case If(t1, t2, t3) => If(renameWithId(t1, x, labelid), renameWithId(t2, x, labelid), renameWithId(t3, x, labelid))
    // These are for lambda calculus
    case Var(y) if y == x => Var(labelid)
    case Var(y) if y != x => t
    case Abs(y, ty, t1) if y == x => Abs(labelid, ty, renameWithId(t1, x, labelid))
    case Abs(y, ty, t1) if y != x => Abs(y, ty, renameWithId(t1, x, labelid))
    case App(t1, t2) => App(renameWithId(t1, x, labelid), renameWithId(t2, x, labelid))
    case _ => t

  def FV(t: Term): List[String] = 
    def FV_helper(t: Term, fv_list: List[String]): List[String] = t match
      // Boolean, Numeric
      case True => fv_list
      case False => fv_list    
      case Zero => fv_list
      case IsZero(t0)  => fv_list ++ FV_helper(t0, fv_list)
      case Succ(t0)  => fv_list ++ FV_helper(t0, fv_list)
      case Pred(t0)  => fv_list ++ FV_helper(t0, fv_list)
      // These are for Pair
      case First(t0) => fv_list ++ FV_helper(t0, fv_list)
      case Second(t0) => fv_list ++ FV_helper(t0, fv_list)
      case TermPair(t1, t2) => fv_list ++ FV_helper(t1, List()) ++ FV_helper(t2, List())
      // For if 
      case If(t1, t2, t3) => fv_list ++ FV_helper(t1, List()) ++ FV_helper(t2, List()) ++ FV_helper(t3, List()) 
      // Lambda Calculus
      case Var(x) => x :: fv_list
      case Abs(x, ty, t1) => FV_helper(t1, fv_list).filter(y => y != x)
      case App(t1, t2) => fv_list ++ FV_helper(t1, List()) ++ FV_helper(t2, List())
    FV_helper(t, List())

  // Combines what we have done in lab1 and lab2
  def subst(t: Term, x: String, s: Term): Term = t match 
      // Boolean, Numeric
      case IsZero(t0) => IsZero(subst(t0, x, s))
      case Succ(t0)  => Succ(subst(t0, x, s))
      case Pred(t0)  => Pred(subst(t0, x, s))
      // These are for Pair
      case First(t0) => First(subst(t0, x, s))
      case Second(t0) => Second(subst(t0, x, s))
      case TermPair(t1, t2) => TermPair(subst(t1, x, s), subst(t2, x, s))
      // For if 
      case If(t1, t2, t3) => If(subst(t1, x, s), subst(t2, x, s), subst(t3, x, s)) 
      // Lambda Calculcus
      case Var(y) if y == x => s
      case Var(y) if y != x => t
      case Abs(y, ty, t1) if y == x => t
      case Abs(y, ty, t1) if y != x && ! FV(s).contains(y) => Abs(y, ty, subst(t1, x, s))
      case Abs(y, ty, t1) if y != x && FV(s).contains(y) => subst(alpha(Abs(y, ty, t1)), x, s)
      case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
      case _ => t

  /** helper function from lab1
  To check if it a numeric */
  def isNumeric(t : Term) : Boolean = t match
    case Zero => true 
    // case Pred(v) => isNumeric(v)
    case Succ(v) => isNumeric(v)
    // TODO: not sure if and Pred
    case _ => false

  def isValue(t:Term):Boolean = t match
    case True => true
    case False => true
    case TermPair(t1, t2) => isValue(t1) && isValue(t2)
    case Abs(_, _, _) => true
    case _=> isNumeric(t)

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match
    case If(cond, t1, t2) => cond match
      case True => t1
      case False => t2 
      case _ => If(reduce(cond), t1, t2)
    case IsZero(v) => v match
      case Zero => True
      case Succ(m) =>
        if isNumeric(m) then False
        else throw new NoRuleApplies(m)
      // else throw new NoRuleApplies(v)
      case _ => IsZero(reduce(v))
    case Pred(v) => v match
      case Zero => Zero
      case Succ(m) =>       
        if isNumeric(m) then m
        else throw new NoRuleApplies(m)
      // else throw new NoRuleApplies(v)
      case _ => Pred(reduce(v))
    case Succ(v) => Succ(reduce(v))
    // lambda calculus: not sure
    case App(Abs(x, type1, t1), t2) if isValue(t2) => subst(t1,x,t2)
    case App(t1, t2) if !isValue(t1) => App(reduce(t1),t2)
    case App(t1, t2) if isValue(t1) && !isValue(t2) => App(t1,reduce(t2))
    // Pair
    case First(TermPair(t1,t2)) if isValue(t1) && isValue(t2)=> t1
    case First(t0) => First(reduce(t0))
    case Second(TermPair(t1,t2)) if isValue(t1) && isValue(t2)=> t2
    case Second(t0) => Second(reduce(t0))
    case TermPair(t1,t2) if !isValue(t1) => TermPair(reduce(t1), t2)
    case TermPair(t1,t2) if isValue(t1) && !isValue(t2) => TermPair(t1, reduce(t2))
    case _=> throw NoRuleApplies(t)


  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
def typeof(ctx: Context, t: Term): Type = t match
  case True => TypeBool
  case False => TypeBool
  case Zero => TypeNat
  case Pred(nv) => 
      val argtype = typeof(ctx, nv)
      if argtype == TypeNat then TypeNat 
      else throw TypeError(t, "Can only take pred of numeric value, not"+argtype)
  case Succ(nv) => 
      val argtype = typeof(ctx, nv)
      if argtype == TypeNat then TypeNat
      else throw TypeError(t, "Can only take succ of numeric value, not "+argtype)
  case IsZero(nv) => 
      val argtype = typeof(ctx, nv)
      if argtype == TypeNat then TypeBool
      else throw TypeError(t, "iszero is expecting a numeric value but got "+argtype)
  case If(t1, t2, t3) => 
    val cond_type = typeof(ctx, t1)
    if cond_type != TypeBool then
      throw TypeError(t, "Condition in if statement should be a boolean, got "+cond_type)
    else if typeof(ctx, t2) == typeof(ctx, t3) then
      typeof(ctx, t2)
    else
      throw TypeError(t, "Both branches in if statement should be of the same type")
  case Var(x) => 
    find_in_context(ctx, x) match
      case None => throw TypeError(t, "Undeclared variable "+x) 
      case Some(x_type) => x_type
  case Abs(x, x_type, t1) => TypeFun(x_type, typeof((x, x_type) :: ctx, t1))
  case App(t1, t2) =>
    typeof(ctx, t1) match
      case TypeFun(a, b) =>
        val argtype = typeof(ctx, t2)
        if argtype == a then b else 
          throw TypeError(t, "Argument type mismatch: expected "+a+", found "+argtype)
      case _ => throw TypeError(t, "Lambda abstraction expected in application")
  case TermPair(t1, t2) => TypePair(typeof(ctx, t1), typeof(ctx, t2))
  case First(pair) =>
    typeof(ctx, pair) match
      case TypePair(a, b) => a
      case o => throw TypeError(t, "fst is expecting a pair but got a "+o)
  case Second(pair) =>
    typeof(ctx, pair) match
      case TypePair(a, b) => b
      case o => throw TypeError(t, "snd is expecting a pair but got a "+o)

  def find_in_context(ctx: Context, key: String): Option[Type] = 
     ctx match
      case Nil => None
      case _ =>
        ctx.head match
          case (head_key, head_type) if head_key == key => Some(head_type)
          case _ => find_in_context(ctx.tail, key)
      




  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): LazyList[Term] =
    try {
      var t1 = reduce(t)
      LazyList.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        LazyList.cons(t, LazyList.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        try {
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
