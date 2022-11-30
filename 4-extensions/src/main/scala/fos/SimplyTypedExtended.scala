package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTypedExtended extends  StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*", "+",
                              "=>", "|")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd", "fix", "letrec",
                              "case", "of", "inl", "inr", "as")


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
   *               | "inl" t "as" T
   *               | "inr" t "as" T
   *               | "case" t "of" "inl" ident "=>" t "|" "inr" ident "=>" t
   *               | "fix" t
   *               | "letrec" ident ":" T "=" t "in" t
   */

  def parseNumeric(n : Int) : Term = 
    if n == 0 then Zero
    else Succ(parseNumeric(n - 1) )
  
  def simple_parse_type: Parser[Type] = 
    "Bool" ^^^ TypeBool |
    "Nat" ^^^ TypeNat | 
    "(" ~ parse_type ~ ")" ^^{ case _ ~ t ~ _ => t}

  def ps_parse_type: Parser[Type] = 
    simple_parse_type ~ "+" ~ ps_parse_type ^^ {case ty1 ~ _ ~ ty2 => TypeSum(ty1, ty2)} |
    simple_parse_type ~ "*" ~ ps_parse_type ^^ {case ty1 ~ _ ~ ty2 => TypePair(ty1, ty2)} | 
    simple_parse_type

  def parse_type: Parser[Type] = repsep(ps_parse_type, "->") ^^ { case list=>list.reduceRight((t1, t2)=>TypeFun(t1, t2)) }

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
    } |
    // The following is for sum
    "inl" ~ term ~ "as" ~ parse_type ^^ {case _ ~ t1 ~ _ ~ ty => Inl(t1,ty)} | 
    "inr" ~ term ~ "as" ~ parse_type ^^ {case _ ~ t1 ~ _ ~ ty => Inr(t1,ty)} | 
    "case" ~ term ~ "of" ~ "inl" ~ ident ~ "=>" ~ term ~ "|" ~ "inr" ~ ident ~ "=>" ~ term ^^ {
      case _ ~ t ~ _ ~ _ ~ s1 ~ _ ~ t1 ~ _ ~ _ ~ s2 ~ _ ~ t2 => Case(t,s1,t1,s2,t2)
    } |
    // The following is for recur
    "fix" ~ term ^^ {case _ ~ t => Fix(t)} | 
    "letrec" ~ ident ~ ":" ~ parse_type ~ "=" ~ term ~ "in" ~ term ^^ { case _ ~ s1 ~ _ ~ ty ~ _ ~ t1 ~ _ ~ t2 => App(Abs(s1, ty, t2), Fix(Abs(s1, ty, t1)))}  

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
    // Case
    case Case(cond,s1,t1,s2,t2) => Case(renameWithId(cond,x, labelid), 
      s1, if (s1==x) t1 else renameWithId(t1,x, labelid), 
      s2, if (s2==x) t2 else renameWithId(t2,x, labelid)
    )
    // Fix
    case Fix(t1) => Fix(renameWithId(t1,x, labelid))
    case _ => t

  def FV(t: Term): List[String] = 
    def FV_helper(t: Term, fv_list: List[String]): List[String] = t match
      // Boolean, Numeric
      case True => fv_list
      case False => fv_list    
      case Zero => fv_list
      case IsZero(t0)  => fv_list ++ FV_helper(t0, List())
      case Succ(t0)  => fv_list ++ FV_helper(t0, List())
      case Pred(t0)  => fv_list ++ FV_helper(t0, List())
      // These are for Pair
      case First(t0) => fv_list ++ FV_helper(t0, List())
      case Second(t0) => fv_list ++ FV_helper(t0, List())
      case TermPair(t1, t2) => fv_list ++ FV_helper(t1, List()) ++ FV_helper(t2, List())
      // For if 
      case If(t1, t2, t3) => fv_list ++ FV_helper(t1, List()) ++ FV_helper(t2, List()) ++ FV_helper(t3, List()) 
      // Lambda Calculus
      case Var(x) => x :: fv_list
      case Abs(x, ty, t1) => FV_helper(t1, fv_list).filter(y => y != x)
      case App(t1, t2) => fv_list ++ FV_helper(t1, List()) ++ FV_helper(t2, List())
      case Inl(t0, ty) => fv_list ++ FV_helper(t0, List())
      case Inr(t0, ty) => fv_list ++ FV_helper(t0, List())
      case Case(cond,s1,t1,s2,t2) => fv_list ++ FV_helper(cond,List()) ++ (FV_helper(t1, List()) diff List(s1)) ++ (FV_helper(t2, List()) diff List(s1))
      case Fix(t1) => FV(t1)
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
      // Sum
      case Inl(t0, ty) => Inl(subst(t0, x, s), ty)
      case Inr(t0, ty) => Inr(subst(t0, x, s), ty)
      case Case(cond, s1, t1, s2, t2) => {
        val subst1 = subst(Abs(s1,TypeNat, t1), x, s).asInstanceOf[Abs]
        val subst2 = subst(Abs(s2,TypeNat, t2), x, s).asInstanceOf[Abs]
        Case(subst(cond, x, s), subst1.v, subst1.t, subst2.v, subst2.t)
      }
      // Fix
      case Fix(t1) => Fix(subst(t1,x,s))
      case _ => t

  
  /** Call by value reducer with a store. */
  def reduce(t: Term, store: Store): (Term, Store) = {
    /* If you implement the imperative bundle, implement this method instead
    * of `reduce(t: Term): Term` below.
    * The default implementation is to always ignore the store.
    */
    (reduce(t), store)
  }
  

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
    case Inl(t1,ty) => isValue(t1)
    case Inr(t1,ty) => isValue(t1)
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
    // Sum 
    case Inl(t0, ty) => Inl(reduce(t0), ty)
    case Inr(t0, ty) => Inr(reduce(t0), ty)
    case Case(Inl(v, ty), s1, t1, s2, t2) if isValue(v) => subst(t1, s1, v)
    case Case(Inr(v, ty), s1, t1, s2, t2) if isValue(v) => subst(t2, s2, v)
    case Case(cond, s1, t1, s2, t2) => Case(reduce(cond), s1, t1, s2, t2)
    // Fix 
    case Fix(Abs(x, ty, t0)) => subst(t0, x, t)
    case Fix(t0) => Fix(reduce(t0))
    case _=>throw NoRuleApplies(t)

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString = msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

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
        case o => throw TypeError(t, "fst is expecting a pair but got a " + o)
    case Second(pair) =>
      typeof(ctx, pair) match
        case TypePair(a, b) => b
        case o => throw TypeError(t, "snd is expecting a pair but got a " + o)
    // Sum
    case Case(cond1, x1, t1, x2, t2) => 
      typeof(ctx, cond1) match
        case TypeSum(ty1, ty2) if typeof((x1, ty1) :: ctx, t1) == typeof((x2, ty2) :: ctx, t2)  => typeof((x2, ty2) :: ctx, t2)
        case o => throw TypeError(t, "Type error with Sum, " + o)   
    case Inl(t1, ty1) => ty1 match
      case TypeSum(ty2, ty3) if typeof(ctx, t1) == ty2 => ty1
      case o => throw TypeError(t, "Type error with Inl, " + o)  
    case Inr(t1, ty1) => ty1 match 
      case TypeSum(ty2, ty3) if typeof(ctx, t1) == ty3 => ty1
      case o => throw TypeError(t, "Type error with Inr, " + o) 
    // Fix
    case Fix(t1) =>
      typeof(ctx,t1) match
        case TypeFun(ty1,ty2) if ty1==ty2 => ty1
        case o => throw TypeError(t, "Type Error with fix, " + o)

    case _=> throw TypeError(t,"Type Error: No parameter type can be matched")

  def find_in_context(ctx: Context, key: String): Option[Type] = 
     ctx match
      case Nil => None
      case _ =>
        ctx.head match
          case (head_key, head_type) if head_key == key => Some(head_type)
          case _ => find_in_context(ctx.tail, key)

  def typeof(t: Term): Type = try {
    typeof(Nil, t)
  } catch {
    case err @ TypeError(_, _) =>
      Console.println(err)
      null
  }

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
          println("parsed: " + trees)
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
