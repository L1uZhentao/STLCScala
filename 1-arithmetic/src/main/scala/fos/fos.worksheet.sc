import fos.Arithmetic._
def input(str: String) = new lexical.Scanner(str)
def parse[T](str: String, parser: Parser[T]) =
    phrase(parser)(input(str))

parse("iszero zero", term)
parse("iszero 0", term)
