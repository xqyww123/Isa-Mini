(* agent_hint.ML — Agent Hint Registry (用时提示机制)

   A theory-local registry of constants / facts that, when the AoA/Minilang
   agent *uses* them (writes them into an authored term, or references a fact
   by name), raises a hint:

     - `Notice` : a soft note is reported back to the agent (via the reporter
                  message channel) and the operation still proceeds;
     - `Reject` : the operation fails with the note as the correction message
                  (`Minilang.OPR_FAIL`), so the bad name never enters the goal.

   The motivating case is `Rat.of_int` (a code-generation shell constant the
   `of_int_*` lemmas do not apply to) vs the coercion `rat_of_int`.

   The third kind of entry is the goal hint (docs/GOAL_HINTS.md): a notice
   keyed on the shape of a goal's conclusion, computed by `goal_hints` where a
   state's leading goal is packed for Python and shown by the footer that asks
   for that goal's proof. The fourth is the auto-Intro exemption
   (docs/AUTO_INTRO_DECISION.md): a pattern over the same positions; a goal
   matching one has the verdict No_Intro in the exemptions' layer of
   `Auto_Intro.verdict_of` (Agent/agent_auto_intro.ML), which asks the
   auto-Intro hooks first. These two kinds share the positions of a goal and
   the pair of nets over them: `Goal_Positions` (the connective table, the
   binder rule, the walk) and the functor `Goal_Patterns` (the two nets,
   applied twice by `Agent_Hint`) sit at the top of this file, at top level
   because Poly/ML allows a functor only there.

   This is intentionally decoupled from `infra_filter` (collection-time
   filtering) and `semantic_store`'s `coercion_ignores` (query-time matching):
   the SemanticDB still indexes the registered names; only the agent's *use*
   of them is intercepted. See agent_hint requirements report. *)


(*** The positions of a goal (docs/GOAL_HINTS.md, section 2) ***)

signature GOAL_POSITIONS =
sig
  (* The two kinds of pattern, named after the positions they are matched at:
     whole_prop at the proposition positions, subterm at every position. *)
  datatype kind = Whole_Prop | Subterm
  val kind_name : kind -> string
  (* The symbol of a connective of the table (section 2.2), as the declaration
     check prints it; HOL.eq is one only at type bool. *)
  val connective_symbol : term -> string option
  (* One walk over the positions of a goal (sections 2.2 and 2.3), folding f
     over each with the flag "this node lies in the propositional structure";
     with term_positions false only the proposition positions are visited
     (section 2.4). A fully applied connective of the table is not a position:
     the walk dispatches on its arguments' roles; every other node is a
     position, a proposition position inside the structure. *)
  val fold_positions : Proof.context -> {term_positions : bool} ->
    (bool -> term -> 'a -> 'a) -> term -> 'a -> 'a
end

structure Goal_Positions : GOAL_POSITIONS =
struct

datatype kind = Whole_Prop | Subterm

fun kind_name Whole_Prop = "whole_prop"
  | kind_name Subterm = "subterm"

(* The role of an argument of a fully applied connective of the table inside
   the propositional structure (section 2.2): in the structure, a term
   position, a binder's argument opened into the structure, or not visited.
   Outside the structure every argument is visited outside it, a binder's
   argument opened by the binder rule. *)
datatype role = Prop | Term | Body | Skip

val connectives =
 [(\<^const_name>\<open>HOL.conj\<close>, ("\<and>", [Prop, Prop])),
  (\<^const_name>\<open>HOL.disj\<close>, ("\<or>", [Prop, Prop])),
  (\<^const_name>\<open>HOL.implies\<close>, ("\<longrightarrow>", [Skip, Prop])),
  (\<^const_name>\<open>HOL.eq\<close>, ("\<longleftrightarrow>", [Prop, Prop])),
  (\<^const_name>\<open>HOL.All\<close>, ("\<forall>", [Body])),
  (\<^const_name>\<open>HOL.Ex\<close>, ("\<exists>", [Body])),
  (\<^const_name>\<open>HOL.Ex1\<close>, ("\<exists>!", [Body])),
  (\<^const_name>\<open>Ball\<close>, ("\<forall>x\<in>A", [Skip, Body])),
  (\<^const_name>\<open>Bex\<close>, ("\<exists>x\<in>A", [Term, Body])),
  (\<^const_name>\<open>Pure.imp\<close>, ("\<Longrightarrow>", [Skip, Prop])),
  (\<^const_name>\<open>Pure.all\<close>, ("\<And>", [Body])),
  (\<^const_name>\<open>Trueprop\<close>, ("Trueprop", [Prop]))]

fun connective (Const (c, T)) =
      if c = \<^const_name>\<open>HOL.eq\<close>
         andalso not (case binder_types T of T1 :: _ => T1 = HOLogic.boolT | [] => false)
      then NONE
      else AList.lookup (op =) connectives c
  | connective _ = NONE

val connective_symbol = Option.map #1 o connective

(*the roles of args when h applied to args is a fully applied connective*)
fun dissolved h args =
  (case connective h of
     SOME (_, roles) => if length roles = length args then SOME roles else NONE
   | NONE => NONE)

(* The binder rule (section 2.1): a binder's argument f, opened with a fresh
   fixed variable of its domain type -- the body of an abstraction, the
   application f x of an eta-contracted f. *)
fun open_binder ctxt f =
  let
    val (x, T) = (case f of Abs (x, T, _) => (x, T) | _ => ("x", domain_type (fastype_of f)))
    val (xs, ctxt') = Variable.variant_fixes [if x = "" then "x" else x] ctxt
  in (ctxt', Term.betapply (f, Free (the_single xs, T))) end

fun fold_positions ctxt {term_positions} f goal acc =
  let
    fun walk ctxt prop t =
      if not prop andalso not term_positions then I
      else
        let val (h, args) = strip_comb t in
          (case dissolved h args of
             SOME roles => fold2 (argument ctxt prop) roles args
           | NONE =>
               f prop t
               #> (case t of
                     Abs _ => walk_body ctxt false t
                   | g $ a => walk ctxt false g #> walk ctxt false a
                   | _ => I))
        end
    and walk_body ctxt prop g =
      let val (ctxt', body) = open_binder ctxt g in walk ctxt' prop body end
    and argument ctxt prop Prop a = walk ctxt prop a
      | argument ctxt _ Term a = walk ctxt false a
      | argument ctxt prop Skip a = if prop then I else walk ctxt false a
      | argument ctxt prop Body a = walk_body ctxt prop a
  in walk ctxt true (Envir.beta_norm goal) acc end

end


(*** Patterns over the positions ***)

(* The elements filed under patterns of the two kinds: a whole_prop net and a
   subterm net over `iNet_Collection`, keyed by `key_of`, the pattern of an
   element. The nets stay inside: a goal is only ever matched with the key its
   elements were filed under. Goal hints and auto-Intro exemptions are its two
   applications (`Agent_Hint`). *)

signature GOAL_PATTERNS =
sig
  type T
  (* files an element under its pattern, in the net of the kind *)
  val add : Goal_Positions.kind -> T -> Context.generic -> Context.generic
  (* folds f over the elements whose pattern matches a goal at a position of
     the walk -- the subterm net's at every position, the whole_prop net's at
     the proposition positions, Pattern.matches deciding (section 2.4); nothing
     is walked when both nets are empty *)
  val fold_matches : Proof.context -> (T -> 'a -> 'a) -> term -> 'a -> 'a
end

functor Goal_Patterns(
  type T
  val eq : T * T -> bool
  val key_of : T -> term) : GOAL_PATTERNS =
struct

type T = T

structure Whole_Prop_Net = iNet_Collection(type T = T  val eq = eq  val key_of = key_of)
structure Subterm_Net = iNet_Collection(type T = T  val eq = eq  val key_of = key_of)

fun add Goal_Positions.Whole_Prop = Whole_Prop_Net.add
  | add Goal_Positions.Subterm = Subterm_Net.add

fun fold_matches ctxt f goal acc =
  let
    val context = Context.Proof ctxt
    val whole_net = Whole_Prop_Net.get_net context
    val sub_net = Subterm_Net.get_net context
    val any_whole = not (iNet.is_empty whole_net)
    val any_sub = not (iNet.is_empty sub_net)
    val thy = Proof_Context.theory_of ctxt
    (*a net keys on term skeletons and over-approximates; Pattern.matches confirms*)
    fun hits net t = filter (fn x => Pattern.matches thy (key_of x, t)) (iNet.match_term net t)
    fun at prop t =
      (any_sub ? fold f (hits sub_net t))
      #> ((prop andalso any_whole) ? fold f (hits whole_net t))
  in
    if not any_whole andalso not any_sub then acc
    else Goal_Positions.fold_positions ctxt {term_positions = any_sub} at goal acc
  end

end


(*** The Agent Hint Registry ***)

signature AGENT_HINT = sig
  datatype severity = Notice | Reject
  (* Carries a notice back to the Python side over the reporter channel.
     `name` is the registered (fully-qualified) const / fact name; it is the
     dedup key the Python `Session` uses for one-shot-per-session display. *)
  exception HINT_NOTICE of {name: string, text: string}
  (* True when at least one constant hint is registered — lets callers skip an
     extra parse-for-checking on the hot path when nothing is registered. *)
  val has_const_hints : Proof.context -> bool
  (* Walk all `Const`s of an agent-authored term and fire any registered hint.
     Reject takes precedence (first reject aborts); notices are reported. *)
  val check_term : Proof.context -> term -> unit
  (* Fire any registered hint on agent-referenced facts (keyed by the resolved
     thm's name hint). A no-op (no fact resolution) when no fact hints exist. *)
  val check_fact_refs : Proof.context -> (Facts.ref * Token.src list) list -> unit
  (* Like check_fact_refs but for already-resolved thms (e.g. a CaseSplit /
     Induction `rule`). *)
  val check_thms : Proof.context -> thm list -> unit
  (* A goal hint (docs/GOAL_HINTS.md). The serial orders the hints and is the
     Python side's dedup key, "goal:<serial>". *)
  type goal_hint = {serial : serial, text : string}
  (* The hints of a leading goal (as `Minilang.leading_goal_data` gives it), in
     declaration order; [] when nothing is registered. Never raises. *)
  val goal_hints : Proof.context -> term -> goal_hint list
  (* The ML entry of `aoa_notice_goal` (docs/GOAL_HINTS.md, section 1): one
     hint over patterns given as text, each read in pattern mode in the
     context and checked as the attribute checks it; the serial is allocated
     at this call, so one call is one hint. *)
  val add_goal_hint : {text : string, whole_prop : string list, subterm : string list} ->
    Context.generic -> Context.generic
  (* The auto-Intro exemptions (docs/AUTO_INTRO_DECISION.md): true when a
     leading goal (as `Minilang.leading_goal_data` gives it) matches a
     registered pattern at a position of the goal hints' walk -- the
     exemptions' layer of `Auto_Intro.verdict_of`. Never raises; false when
     nothing is registered. *)
  val exempt_from_auto_intro : Proof.context -> term -> bool
  (* The ML entry of `aoa_no_auto_intro` (docs/AUTO_INTRO_DECISION.md,
     section 3): the patterns given as text, each read in pattern mode in the
     context and checked as the attribute checks it. *)
  val add_auto_intro_exemption : {whole_prop : string list, subterm : string list} ->
    Context.generic -> Context.generic
end

structure Agent_Hint : AGENT_HINT = struct

datatype severity = Notice | Reject

exception HINT_NOTICE of {name: string, text: string}

(* (const_table, fact_table), each mapping a fully-qualified name to its
   (severity, message). *)
structure Data = Generic_Data(
  type T = (severity * string) Symtab.table * (severity * string) Symtab.table
  val empty = (Symtab.empty, Symtab.empty)
  fun merge ((c1, f1), (c2, f2)) =
    (Symtab.merge (K true) (c1, c2), Symtab.merge (K true) (f1, f2))
)

fun add_const entry = Data.map (apfst (Symtab.update entry))
fun add_fact entry = Data.map (apsnd (Symtab.update entry))

(* Fire one registered hit. A reject uses `OTHER` (not `TERMLANG`): the term
   parsed fine and is then rejected on policy grounds, so the message must be
   surfaced verbatim with no "Syntax Error in Term Language" framing. *)
fun fire (_, (Reject, text)) =
      raise Minilang.OPR_FAIL (Minilang.OTHER, text)
  | fire (name, (Notice, text)) =
      Minilang.get_reporter () (Minilang.Internal (HINT_NOTICE {name = name, text = text}))

fun has_const_hints ctxt = not (Symtab.is_empty (#1 (Data.get (Context.Proof ctxt))))

fun check_term ctxt t =
  let val (ctab, _) = Data.get (Context.Proof ctxt) in
    if Symtab.is_empty ctab then ()
    else
      let
        val hits =
          Term.add_const_names t []
          |> map_filter (fn n => Option.map (pair n) (Symtab.lookup ctab n))
        val (rejects, notices) =
          List.partition (fn (_, (sev, _)) => sev = Reject) hits
      in
        (case rejects of hit :: _ => fire hit | [] => List.app fire notices)
      end
  end

(* `Thm.get_name_hint` returns this sentinel for a nameless thm; it must never
   be used as a registry key (it would match every other nameless thm). *)
val nameless_thm = "??.unknown"

fun check_thm ftab th =
  let val name = #1 (Thm.get_name_hint th) in
    if name = nameless_thm then ()
    else (case Symtab.lookup ftab name of SOME e => fire (name, e) | NONE => ())
  end

(* Register a fact hint keyed by the thm's name hint; skip nameless thms so we
   never create a `"??.unknown"` key. Used by the `aoa_notice`/`aoa_reject`
   fact attributes. *)
fun add_fact_hint sev text th =
  let val name = #1 (Thm.get_name_hint th) in
    if name = nameless_thm then I else add_fact (name, (sev, text))
  end

fun check_fact_refs ctxt refs =
  let val (_, ftab) = Data.get (Context.Proof ctxt) in
    if Symtab.is_empty ftab then ()
    else
      (* Resolve each ref to thms for keying; a ref that fails to resolve is left
         for the op's own (authoritative) resolution to report — scanning must
         not change behaviour. A reject from `check_thm` (OPR_FAIL) propagates. *)
      List.app (fn r =>
        List.app (check_thm ftab) (Attrib.eval_thms ctxt [r] handle ERROR _ => [])) refs
  end

fun check_thms ctxt ths =
  let val (_, ftab) = Data.get (Context.Proof ctxt) in
    if Symtab.is_empty ftab then () else List.app (check_thm ftab) ths
  end

(* Declaration attributes:
     declare [[aoa_notice_constant <const> "..."]]
     declare [[aoa_reject_constant <const> "..."]]
     declare <fact> [aoa_notice "..."]
     declare <fact> [aoa_reject "..."]
   The constant attributes follow the `coercion`/`coercion_args` idiom
   (`Args.const` resolves to the fully-qualified name at declaration time, so
   matching is immune to short-name/ambiguity); they ignore the (empty) fact.
   The fact attributes key on `Thm.get_name_hint`. *)
val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>aoa_notice_constant\<close>
      (Args.const {proper = true, strict = false} -- Scan.lift Parse.embedded >>
        (fn (c, text) => Thm.declaration_attribute (K (add_const (c, (Notice, text))))))
      "register an agent NOTICE hint on a constant the agent should avoid" #>
    Attrib.setup \<^binding>\<open>aoa_reject_constant\<close>
      (Args.const {proper = true, strict = false} -- Scan.lift Parse.embedded >>
        (fn (c, text) => Thm.declaration_attribute (K (add_const (c, (Reject, text))))))
      "register an agent REJECT hint on a constant the agent must not use" #>
    Attrib.setup \<^binding>\<open>aoa_notice\<close>
      (Scan.lift Parse.embedded >>
        (fn text => Thm.declaration_attribute (add_fact_hint Notice text)))
      "register an agent NOTICE hint on a fact the agent should avoid" #>
    Attrib.setup \<^binding>\<open>aoa_reject\<close>
      (Scan.lift Parse.embedded >>
        (fn text => Thm.declaration_attribute (add_fact_hint Reject text)))
      "register an agent REJECT hint on a fact the agent must not use")


(*** Goal hints (docs/GOAL_HINTS.md) and auto-Intro exemptions
     (docs/AUTO_INTRO_DECISION.md): patterns over the same positions ***)

type goal_hint = {serial : serial, text : string}

(* One element per (pattern, hint): a hint with n patterns is n elements. The
   key is the pattern, so a match returns the (pattern, hint) pairs directly. *)
fun eq_pattern ((p1, h1 : goal_hint), (p2, h2 : goal_hint)) =
  #serial h1 = #serial h2 andalso p1 aconv p2

structure Goal_Hint_Patterns = Goal_Patterns(
  type T = term * goal_hint
  val eq = eq_pattern
  val key_of = fst)

(* An exemption is its pattern: the same pattern declared twice is one
   element. *)
structure Exemption_Patterns = Goal_Patterns(
  type T = term
  val eq = op aconv
  val key_of = I)

(*the hints matched, each once, in declaration order*)
fun goal_hints ctxt goal =
  Goal_Hint_Patterns.fold_matches ctxt
    (fn (_, hint : goal_hint) => Inttab.update (#serial hint, hint)) goal Inttab.empty
  |> Inttab.dest |> map #2

(*a match is the verdict No_Intro in the exemptions' layer of Auto_Intro.verdict_of*)
fun exempt_from_auto_intro ctxt goal =
  Exemption_Patterns.fold_matches ctxt (K (K true)) goal false


(* The attributes (docs/GOAL_HINTS.md section 1; docs/AUTO_INTRO_DECISION.md
   section 3):
     declare [[aoa_notice_goal "text" clause ...]]
     declare [[aoa_no_auto_intro clause ...]]
     clause   ::= whole_prop patterns | subterm patterns
     patterns ::= "pattern" (and "pattern")*
   A pattern is read in pattern mode in the declaring context and stored
   beta-eta contracted; the three checks run on that term. *)

fun add_pattern hint (kind, (_, pat)) = Goal_Hint_Patterns.add kind (pat, hint)

fun add_exemption (kind, (_, pat)) = Exemption_Patterns.add kind pat

(* The checks, on the pattern as stored, quoting it as the author wrote it
   after `declaration`, the name of what is declared in the message. *)
fun check_pattern declaration ctxt (kind, (src, pat)) =
  let
    val what = declaration ^ " " ^ Goal_Positions.kind_name kind ^ " " ^ quote src ^ ": "
    val T = fastype_of pat
    val _ =
      kind = Goal_Positions.Whole_Prop
      andalso not (can (Sign.typ_match (Proof_Context.theory_of ctxt) (T, HOLogic.boolT)) Vartab.empty)
      andalso error (what ^ "its type is " ^
                     Syntax.string_of_typ (Config.put show_sorts true ctxt) T ^ ", not bool")
    val _ =
      (case Goal_Positions.connective_symbol (Term.head_of pat) of
         SOME symbol => error (what ^ "it contains the connective " ^ symbol)
       | NONE => ())
    val _ =
      (case rev (Variable.add_frees ctxt pat []) of
         [] => ()
       | (x, _) :: _ =>
           error (what ^ x ^ " is neither a constant nor fixed here; write _ or ?" ^ x ^
                  " for an open position, or import the theory that defines it"))
  in () end

(* the token keeps the text the author wrote: a term read in pattern mode
   cannot be printed back faithfully *)
val pattern =
  Scan.lift (Scan.ahead Parse.embedded) -- Args.term_pattern >> apsnd Envir.beta_eta_contract

val patterns = Parse.and_list1' pattern

fun clause kind =
  Scan.lift (Args.$$$ (Goal_Positions.kind_name kind)) |-- Parse.!!!! patterns >> map (pair kind)

val clauses = Scan.repeat1 (clause Goal_Positions.Whole_Prop || clause Goal_Positions.Subterm)

(* The checks, then the one hint over its patterns as a declaration. The serial
   is allocated here, once: a declaration is one hint however many patterns it
   carries and however many facts the attribute is applied to. *)
fun goal_hint_declaration ctxt text patterns =
  let
    val _ = List.app (check_pattern "Goal hint" ctxt) patterns
    val hint = {serial = serial (), text = text}
  in fold (add_pattern hint) patterns end

(*the checks, then the exemptions as a declaration*)
fun auto_intro_exemption_declaration ctxt patterns =
  let val _ = List.app (check_pattern "Auto-Intro exemption" ctxt) patterns
  in fold add_exemption patterns end

(* The patterns of the two clauses given as text, read as the attributes read
   them, with the context they are read in. *)
fun read_patterns context {whole_prop, subterm} =
  let
    val ctxt = Context.proof_of context
    fun read kind src =
      (kind, (src, Envir.beta_eta_contract (Proof_Context.read_term_pattern ctxt src)))
  in
    (ctxt,
     map (read Goal_Positions.Whole_Prop) whole_prop @ map (read Goal_Positions.Subterm) subterm)
  end

fun add_goal_hint {text, whole_prop, subterm} context =
  let val (ctxt, patterns) = read_patterns context {whole_prop = whole_prop, subterm = subterm}
  in goal_hint_declaration ctxt text patterns context end

fun add_auto_intro_exemption clauses context =
  let val (ctxt, patterns) = read_patterns context clauses
  in auto_intro_exemption_declaration ctxt patterns context end

val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>aoa_notice_goal\<close>
      (Args.context -- Scan.lift Parse.embedded -- clauses >>
        (fn ((ctxt, text), clauses) =>
          Thm.declaration_attribute (K (goal_hint_declaration ctxt text (flat clauses)))))
      "register an AoA notice shown when a goal's conclusion matches a pattern" #>
    Attrib.setup \<^binding>\<open>aoa_no_auto_intro\<close>
      (Args.context -- clauses >>
        (fn (ctxt, clauses) =>
          Thm.declaration_attribute (K (auto_intro_exemption_declaration ctxt (flat clauses)))))
      "exempt the goals matching a pattern from AoA's automatic Intro")

end

(*TEMPORARY hunt marker (`exception Option`, 2026-09-03): forces this session to
  rebuild so its ROOT ML_debugger option takes effect (a ROOT options change alone
  does not enter the session digest).  Delete with the hunt.*)
