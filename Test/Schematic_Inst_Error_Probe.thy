theory Schematic_Inst_Error_Probe
  imports Minilang.Minilang
begin

text \<open>
  Probes error-message quality for two approaches to instantiating
  schematic variables of an induction rule:

  (a) String path — assemble `rule_name[where ?v = t]` as a source
      string, parse via `Attrib.eval_thms` (what Minilang currently
      uses after Phase 3).

  (b) Structured path — parse each term separately, then call
      `Rule_Insts.where_rule` with `(indexname * string) list`.

  Four bad-input cases are tried against `int_le_induct` (which has a
  schematic `?k :: int`):

    1. Syntactic error in the term        (`k +` — incomplete)
    2. Type mismatch with schematic's type (`True` for `?k :: int`)
    3. Unknown free variable in the term  (`undefined_xyz`)
    4. Wrong schematic name               (instantiate `?xyz`, not `?k`)

  Goal: see which path yields errors that are easier to (i) parse
  programmatically, (ii) relay back to the LLM via
  `Interaction_InstantiateSchematics` as a `BadAnswer` reason.
\<close>

ML \<open>
local
  val ctxt = \<^context>
  val rule_name = "int_le_induct"
  val raw_rule = Proof_Context.get_thm ctxt rule_name

  fun run_or_capture label f =
    let
      fun announce tag msg =
        writeln (String.concat ["  ", label, " -- ", tag, ": ", msg])
    in
      (let val _ = f () in announce "UNEXPECTED" "call succeeded, expected an exception" end)
      handle ERROR msg => announce "ERROR" msg
           | TYPE (msg, _, _) => announce "TYPE" msg
           | TERM (msg, _) => announce "TERM" msg
           | THM (msg, _, _) => announce "THM" msg
           | Fail msg => announce "Fail" msg
    end

  fun string_path rule_src =
    let
      val keywords = Thy_Header.get_keywords \<^theory>
      val symbols = Input.source_explode (Input.string rule_src)
      val toks = Token.tokenize keywords {strict = true} symbols
                 |> filter Token.is_proper
      val fact_ref =
        case Scan.read Token.stopper Parse.thm toks of
          SOME fact => fact
        | NONE => error ("Cannot parse `" ^ rule_src ^ "` as a fact reference")
    in Attrib.eval_thms ctxt [fact_ref] end

  (* Structured path: (indexname * Position.T) * string  = raw_inst shape
     expected by Rule_Insts.where_rule. *)
  fun structured_path insts =
    let
      val raw_insts : ((indexname * Position.T) * string) list =
        map (fn (v, t) => ((v, Position.none), t)) insts
    in Rule_Insts.where_rule ctxt raw_insts [] raw_rule end

  fun case_header n desc =
    writeln (String.concat [
      "\n### Case ", string_of_int n, ": ", desc])
in

  val _ = case_header 1 "Syntactic error — term `k +` (incomplete)"
  val _ = run_or_capture "string    "
    (fn () => string_path (rule_name ^ "[where ?k = k +]"))
  val _ = run_or_capture "structured"
    (fn () => structured_path [(("k", 0), "k +")])

  val _ = case_header 2 "Type mismatch — term `True` where ?k :: int"
  val _ = run_or_capture "string    "
    (fn () => string_path (rule_name ^ "[where ?k = True]"))
  val _ = run_or_capture "structured"
    (fn () => structured_path [(("k", 0), "True")])

  val _ = case_header 3 "Unknown free variable in term — `undefined_xyz`"
  val _ = run_or_capture "string    "
    (fn () => string_path (rule_name ^ "[where ?k = undefined_xyz]"))
  val _ = run_or_capture "structured"
    (fn () => structured_path [(("k", 0), "undefined_xyz")])

  val _ = case_header 4 "Wrong schematic name — target ?xyz not in rule"
  val _ = run_or_capture "string    "
    (fn () => string_path (rule_name ^ "[where ?xyz = k]"))
  val _ = run_or_capture "structured"
    (fn () => structured_path [(("xyz", 0), "k")])

  val _ = writeln "\n### Sanity: good instantiation"
  val _ = run_or_capture "string     [EXPECTED success, should report UNEXPECTED]"
    (fn () => string_path (rule_name ^ "[where ?k = k]"))
  val _ = run_or_capture "structured [EXPECTED success, should report UNEXPECTED]"
    (fn () => structured_path [(("k", 0), "k")])
end
\<close>

end
