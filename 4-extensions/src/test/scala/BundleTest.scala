import org.scalatest.flatspec.AnyFlatSpec


import fos.SimplyTypedExtended._
import fos._

def input(str: String) = new lexical.Scanner(str)
def parse(str: String) : Term =
    phrase(term)(input(str)) match {
      case Success(trees, _) =>
        trees
      case e =>
        throw Exception("parse error:"+e)
    }

def reduce_to_end(t: Term) : Term = 
  try {
    reduce_to_end(reduce(t))
  } catch {
    case NoRuleApplies(_) => t
  }


class BundleSpec extends AnyFlatSpec {

  "true" should "be parsed as true" in {
    val input = "true"
    val expected_parse = True
    assertResult(expected_parse){
      parse(input)
    }
  }

  it should "be typed as Bool" in {
    val input = "true"
    val expected_type = TypeBool
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to true" in {
    val input = "true"
    val expected_nf = True
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "succ pred 3" should "be parsed as (succ (pred (succ (succ (succ 0)))))" in {
    val input = "succ pred 3"
    val expected_parse = Succ(Pred(Succ(Succ(Succ(Zero)))))
    assertResult(expected_parse){
      parse(input)
    }
  }

  it should "be typed as Nat" in {
    val input = "succ pred 3"
    val expected_type = TypeNat
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to 3" in {
    val input = "succ pred 3"
    val expected_nf = Succ(Succ(Succ(Zero)))
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "{a=1,b=false,c=iszero 0,}" should "be parsed as {a=(succ 0),b=false,c=(iszero 0),}" in {
    val input = "{a=1,b=false,c=iszero 0,}"
    val expected_parse = Record(List(("a", Succ(Zero)),("b", False),("c", IsZero(Zero))))
    assertResult(expected_parse){
      parse(input)
    }
  }

  it should "be typed as {a: Nat, b: Bool, c Bool}" in {
    val input = "{a=1,b=false,c=iszero 0,}"
    val expected_type = TypeRecord(List(("a", TypeNat), ("b", TypeBool), ("c", TypeBool))) 
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to {a=1,b=false,c=true,}" in {
    val input = "{a=1,b=false,c=iszero 0,}"
    val expected_nf = Record(List(("a", Succ(Zero)),("b", False),("c", True)))
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "{banana=true,apple=false,other=0,}.apple" should "be parsed as {banana=true,apple=false,other=0,}.apple" in {
    val input = "{banana=true,apple=false,other=0,}.apple"
    val expected_parse = RecordProj(Record(List(("banana", True),("apple",False),("other",Zero))),"apple")
    assertResult(expected_parse){
      parse(input)
    }
  }

  it should "be typed as Bool" in {
    val input = "{banana=true,apple=false,other=0,}.apple"
    val expected_type = TypeBool 
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to false" in {
    val input = "{banana=true,apple=false,other=0,}.apple"
    val expected_nf = False
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "{0, true, 0}" should "be parsed as {0=0, 1=true, 2=0,}" in {
    val input = "{0, true, 0,}"
    val expected_parse = Record(List(("0", Zero),("1", True),("2", Zero)))
    assertResult(expected_parse){
      parse(input)
    }
  }

  it should "be typed as {Nat, Bool, Nat}" in {
    val input = "{0, true, 0,}"
    val expected_type = TypeRecord(List(("0", TypeNat), ("1", TypeBool), ("2", TypeNat)))
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to {0, true, 0,}" in {
    val input = "{0, true, 0,}"
    val expected_nf = Record(List(("0", Zero),("1", True),("2", Zero)))
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "{2, 1}.1" should "be parsed as {2, 1,}.1" in {
    val input = "{2, 1,}.1"
    val expected_parse = RecordProj(Record(List(("0", Succ(Succ(Zero))),("1", Succ(Zero)))), "1") 
    assertResult(expected_parse){
      parse(input)
    }
  }

  it should "be typed as Nat" in {
    val input = "{2, 1,}.1"
    val expected_type = TypeNat
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to 1" in {
    val input = "{2, 1,}.1"
    val expected_nf = Succ(Zero)
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "empty record" should "be parsed as {}" in {
    val input = "{}"
    val expected_parse = Record(Nil)
    assertResult(expected_parse){
      parse(input)
    }
  }

  it should "be typed as record" in {
    val input = "{}"
    val expected_type = TypeRecord(Nil)
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to {}" in {
    val input = "{}"
    val expected_nf = Record(Nil)
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "(\\u:{y:Nat,x:Nat,}.if iszero u.x then u.y else u.x) {x=1,y=5}" should "be typed as record" in {
    val input = "(\\u:{y:Nat,x:Nat,}.if iszero u.x then u.y else u.x) {x=1,y=5}"
    val expected_type = TypeNat
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to 1" in {
    val input = "(\\u:{y:Nat,x:Nat,}.if iszero u.x then u.y else u.x) {x=1,y=5}"
    val expected_nf = Succ(Zero)
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "empty list" should "be parsed as empty list" in {
    val input = "nil [Nat]"
    val expected_parse = NilVal(TypeNat)
    assertResult(expected_parse){
      parse(input)
    }
  }

  it should "be typed as List[Nat]" in {
    val input = "nil [Nat]"
    val expected_type = TypeList(TypeNat)
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to itself" in {
    val input = "nil [Nat]"
    val expected_nf = NilVal(TypeNat)
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "cons [Nat] 2 cons [Nat] 0 nil [Nat]" should "be parsed as empty list" in {
    val input = "cons [Nat] 2 cons [Nat] 0 nil [Nat]"
    val expected_parse = Cons(TypeNat, Succ(Succ(Zero)), Cons(TypeNat, Zero, NilVal(TypeNat)))
    assertResult(expected_parse){
      parse(input)
    }
  }

  it should "be typed as List[Nat]" in {
    val input = "cons [Nat] 2 cons [Nat] 0 nil [Nat]"
    val expected_type = TypeList(TypeNat)
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to itself" in {
    val input = "cons [Nat] 2 cons [Nat] 0 nil [Nat]"
    val expected_nf = Cons(TypeNat, Succ(Succ(Zero)), Cons(TypeNat, Zero, NilVal(TypeNat)))
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "case cons [Bool] true nil [Bool] of nil => False | cons head remain => head" should "be typed as Bool" in {
    val input = "case cons [Bool] true nil [Bool] of nil => False | cons head remain => head"
    val expected_type = TypeBool
    assertResult(expected_type){
      typeof(Nil, parse(input))
    }
  }

  it should "evaluate to True" in {
    val input = "case cons [Bool] true nil [Bool] of nil => False | cons head remain => head"
    val expected_nf = True
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "letrec sum = \\x:Nat.\\y:Nat. if iszero x then y else sum (pred x) (succ y) in sum 3 1" should "evaluate to 5" in {
    val input = "letrec sum: Nat->Nat = (\\x:Nat.(\\y:Nat. if iszero x then y else sum (pred x) (succ y))) in sum 3 2"
    val expected_nf = Succ(Succ(Succ(Succ(Succ(Zero)))))
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }

  "letrec sum = \\x:Nat.\\y:Nat. if iszero x then y else sum (pred x) (succ y) in sum 3 1" should "evaluate to [5, 4, 3, 2, 1]" in {
    val input = "letrec seq: Nat->[Nat] = (\\n:Nat.if iszero n then nil [Nat] else cons n (seq (pred n))) in seq 6"
    val expected_nf = Cons(TypeNat, Succ(Succ(Succ(Succ(Succ(Succ(Zero)))))),
                      Cons(TypeNat, Succ(Succ(Succ(Succ(Zero)))),
                      Cons(TypeNat, Succ(Succ(Succ(Zero))),
                      Cons(TypeNat, Succ(Succ(Zero)),
                      Cons(TypeNat, Succ(Zero),
                      NilVal(TypeNat)
                      )))))
    assertResult(expected_nf){
      reduce_to_end(parse(input))
    }
  }
}
