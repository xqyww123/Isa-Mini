theory Test_ArgsVar_Token
  imports Minilang.Minilang
begin

ML \<open>
val test_inputs = ["n", "n2", "?n", "?n2", "n.2", "?n.2"]

val _ = List.app (fn input =>
  let
    val toks = Token.explode (Thy_Header.get_keywords' \<^context>) Position.none input

    val tok_info = String.concatWith ", " (map (fn t =>
        Token.kind_of t |> Token.str_of_kind |> (fn k =>
          k ^ ":" ^ quote (Token.content_of t))) toks)

    (* Try Args.var *)
    val var_result =
      (case Scan.read Token.stopper Args.var toks of
        SOME xi => "var OK: " ^ quote (Term.string_of_vname xi)
      | NONE => "var FAIL")

    (* Try Args.name *)
    val name_result =
      (case Scan.read Token.stopper Args.name toks of
        SOME s => "name OK: " ^ quote s
      | NONE => "name FAIL")

  in writeln (quote input ^ " => tokens=[" ^ tok_info ^ "] | " ^ var_result ^ " | " ^ name_result) end
) test_inputs
\<close>

end
