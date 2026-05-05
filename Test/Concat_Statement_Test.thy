theory Concat_Statement_Test
  imports Main
begin

ML \<open>
(* concat_statement: assemble structured statement pieces into a single prop string.
   fixes: list of (name, type_str) pairs — type_str may be "" for inferred
   assumes: list of term strings (premises)
   concl: conclusion term string
   Returns: pretty-printed prop string like "\<And>x::nat. P x \<Longrightarrow> Q x" *)
fun concat_statement ctxt (fixes: (string * string) list) (assumes: string list) (concl: string) =
  let
    (* 1. Declare Free terms with their types so read_props resolves them *)
    val ctxt1 = ctxt |> Variable.set_body true
    val fix_frees = map (fn (name, typ_str) =>
      let val T = if typ_str = "" then dummyT
                  else Syntax.read_typ ctxt typ_str
      in Free (name, T) end) fixes
    val ctxt2 = fold Variable.declare_term fix_frees ctxt1

    (* 2. Batch-read all props — conclusion first for type propagation *)
    val (concl_prop :: asm_props) = Syntax.read_props ctxt2 (concl :: assumes)

    (* 3. Build implication chain: asm1 \<Longrightarrow> ... \<Longrightarrow> concl *)
    val body = Logic.list_implies (asm_props, concl_prop)

    (* 4. Quantify over fixed variables: \<And>x1 ... xn. body *)
    val fix_names = map fst fixes
    val fix_vars = map (fn name =>
      let val frees = Term.add_frees body []
          val T = case AList.lookup (op =) frees name of
                    SOME T => T
                  | NONE => error ("Fixed variable " ^ quote name ^ " not found in parsed terms")
      in Free (name, T) end) fix_names
    val full = fold_rev Logic.all fix_vars body
  in
    Syntax.string_of_term ctxt full
  end
\<close>

text \<open>Test 1: simple quantified statement\<close>
ML \<open>
let
  val ctxt = \<^context>
  val result = concat_statement ctxt [("x", "nat")] [] "x \<le> x"
  val _ = writeln ("Test 1: " ^ result)
in () end
\<close>

text \<open>Test 2: with a premise\<close>
ML \<open>
let
  val ctxt = \<^context>
  val result = concat_statement ctxt [("x", "nat")] ["x > 0"] "x \<ge> Suc 0"
  val _ = writeln ("Test 2: " ^ result)
in () end
\<close>

text \<open>Test 3: multiple variables and premises\<close>
ML \<open>
let
  val ctxt = \<^context>
  val result = concat_statement ctxt [("x", "nat"), ("y", "nat")] ["x < y", "y < 10"] "x < 10"
  val _ = writeln ("Test 3: " ^ result)
in () end
\<close>

text \<open>Test 4: no quantifiers, just premises\<close>
ML \<open>
let
  val ctxt = \<^context>
  val result = concat_statement ctxt [] ["A", "B"] "A \<and> B"
  val _ = writeln ("Test 4: " ^ result)
in () end
\<close>

text \<open>Test 5: no quantifiers, no premises (bare conclusion)\<close>
ML \<open>
let
  val ctxt = \<^context>
  val result = concat_statement ctxt [] [] "True"
  val _ = writeln ("Test 5: " ^ result)
in () end
\<close>

text \<open>Test 6: inferred type (empty type string)\<close>
ML \<open>
let
  val ctxt = \<^context>
  val result = concat_statement ctxt [("xs", "")] [] "length xs > 0"
  val _ = writeln ("Test 6: " ^ result)
in () end
\<close>

end
