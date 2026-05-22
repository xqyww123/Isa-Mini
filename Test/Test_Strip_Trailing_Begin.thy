theory Test_Strip_Trailing_Begin
  imports Main
begin

ML \<open>
local

fun strip_trailing_begin src =
  let
    val len = size src
    fun rskip i = if i < 0 then i
      else if Char.isSpace (String.sub (src, i)) then rskip (i - 1) else i
    val last = rskip (len - 1)
  in
    if last >= 4 andalso String.substring (src, last - 4, 5) = "begin"
       andalso (last < 5 orelse String.sub (src, last - 5) = #"\n")
    then String.substring (src, 0, if last >= 5 then last - 5 else 0)
    else src
  end

fun assert_eq (label, expected, actual) =
  if expected = actual then ()
  else error (String.concat [
    label, " FAILED\n  expected: ", ML_Syntax.print_string expected,
    "\n  actual:   ", ML_Syntax.print_string actual])

in

val _ = assert_eq ("class with begin",
  "class monoid = semigroup +\n  fixes one :: 'a",
  strip_trailing_begin "class monoid = semigroup +\n  fixes one :: 'a\nbegin")

val _ = assert_eq ("class with begin + trailing whitespace",
  "class monoid = semigroup +\n  fixes one :: 'a",
  strip_trailing_begin "class monoid = semigroup +\n  fixes one :: 'a\nbegin  \n")

val _ = assert_eq ("no begin (datatype)",
  "datatype 'a list = Nil | Cons 'a \"'a list\"",
  strip_trailing_begin "datatype 'a list = Nil | Cons 'a \"'a list\"")

val _ = assert_eq ("locale with begin",
  "locale group =\n  fixes inv",
  strip_trailing_begin "locale group =\n  fixes inv\nbegin")

val _ = assert_eq ("just begin",
  "",
  strip_trailing_begin "begin")

val _ = assert_eq ("empty string",
  "",
  strip_trailing_begin "")

val _ = assert_eq ("begin in middle is kept",
  "something begin more",
  strip_trailing_begin "something begin more")

val _ = assert_eq ("newline then begin",
  "",
  strip_trailing_begin "\nbegin")

val _ = assert_eq ("word ending in begin is kept",
  "let_begin",
  strip_trailing_begin "let_begin")

val _ = writeln "All strip_trailing_begin tests passed."

end
\<close>

end
