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
   for that goal's proof.

   This is intentionally decoupled from `infra_filter` (collection-time
   filtering) and `semantic_store`'s `coercion_ignores` (query-time matching):
   the SemanticDB still indexes the registered names; only the agent's *use*
   of them is intercepted. See agent_hint requirements report. *)

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


(*** Goal hints (docs/GOAL_HINTS.md) ***)

type goal_hint = {serial : serial, text : string}

(* One element per (pattern, hint): a hint with n patterns is n elements. The
   key is the pattern, so a match returns the (pattern, hint) pairs directly. *)
fun eq_pattern ((p1, h1 : goal_hint), (p2, h2 : goal_hint)) =
  #serial h1 = #serial h2 andalso p1 aconv p2

structure Whole_Prop_Patterns = iNet_Collection(
  type T = term * goal_hint
  val eq = eq_pattern
  val key_of = fst)

structure Subterm_Patterns = iNet_Collection(
  type T = term * goal_hint
  val eq = eq_pattern
  val key_of = fst)

(* The role of an argument of a fully applied connective of the table inside
   the propositional structure (section 2.2): in the structure, a term
   position, a binder's argument opened into the structure, or not visited.
   Outside the structure every argument is visited outside it, a binder's
   argument opened by the binder rule. *)
datatype role = Prop | Term | Body | Skip

(* The connectives of the table (section 2.2), each with the symbol the
   declaration check prints and the roles of its arguments. HOL.eq is one
   only at type bool (`connective`). *)
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

(* The roles of args when h applied to args is a fully applied connective of
   the table. *)
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

fun goal_hints ctxt goal =
  let
    val context = Context.Proof ctxt
    val whole_net = Whole_Prop_Patterns.get_net context
    val sub_net = Subterm_Patterns.get_net context
    val any_whole = not (iNet.is_empty whole_net)
    val any_sub = not (iNet.is_empty sub_net)
  in
    if not any_whole andalso not any_sub then []
    else
      let
        val thy = Proof_Context.theory_of ctxt
        (* a net keys on term skeletons and over-approximates; Pattern.matches confirms *)
        fun hits net t =
          map_filter (fn (pat, hint) => if Pattern.matches thy (pat, t) then SOME hint else NONE)
            (iNet.match_term net t)
        fun add_hint (hint : goal_hint) = Inttab.update (#serial hint, hint)
        fun found prop t =
          (any_sub ? fold add_hint (hits sub_net t))
          #> ((prop andalso any_whole) ? fold add_hint (hits whole_net t))

        (* One walk over the positions (sections 2.2 and 2.3) carrying the flag
           "this node lies in the propositional structure", pruned by what is
           registered (section 2.4). A fully applied connective of the table is
           not a position: the walk dispatches on its arguments' roles; every
           other node is a position, a proposition position inside the
           structure. *)
        fun walk ctxt prop t =
          if not prop andalso not any_sub then I
          else
            let val (h, args) = strip_comb t in
              (case dissolved h args of
                 SOME roles => fold2 (argument ctxt prop) roles args
               | NONE =>
                   found prop t
                   #> (case t of
                         Abs _ => walk_body ctxt false t
                       | f $ a => walk ctxt false f #> walk ctxt false a
                       | _ => I))
            end
        and walk_body ctxt prop f =
          let val (ctxt', body) = open_binder ctxt f in walk ctxt' prop body end
        and argument ctxt prop Prop a = walk ctxt prop a
          | argument ctxt _ Term a = walk ctxt false a
          | argument ctxt prop Skip a = if prop then I else walk ctxt false a
          | argument ctxt prop Body a = walk_body ctxt prop a
      in map #2 (Inttab.dest (walk ctxt true (Envir.beta_norm goal) Inttab.empty)) end
  end


(* The attribute (section 1):
     declare [[aoa_notice_goal "text" clause ...]]
     clause   ::= whole_prop patterns | subterm patterns
     patterns ::= "pattern" (and "pattern")*
   A pattern is read in pattern mode in the declaring context and stored
   beta-eta contracted; the three checks run on that term. *)

datatype kind = Whole_Prop | Subterm

fun kind_name Whole_Prop = "whole_prop"
  | kind_name Subterm = "subterm"

fun add_pattern hint (Whole_Prop, (_, pat)) = Whole_Prop_Patterns.add (pat, hint)
  | add_pattern hint (Subterm, (_, pat)) = Subterm_Patterns.add (pat, hint)

(* The checks, on the pattern as stored, quoting it as the author wrote it. *)
fun check_pattern ctxt (kind, (src, pat)) =
  let
    val what = "Goal hint " ^ kind_name kind ^ " " ^ quote src ^ ": "
    val T = fastype_of pat
    val _ =
      kind = Whole_Prop
      andalso not (can (Sign.typ_match (Proof_Context.theory_of ctxt) (T, HOLogic.boolT)) Vartab.empty)
      andalso error (what ^ "its type is " ^
                     Syntax.string_of_typ (Config.put show_sorts true ctxt) T ^ ", not bool")
    val _ =
      (case connective (Term.head_of pat) of
         SOME (symbol, _) => error (what ^ "it contains the connective " ^ symbol)
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

fun clause kind = Scan.lift (Args.$$$ (kind_name kind)) |-- Parse.!!!! patterns >> map (pair kind)

val clauses = Scan.repeat1 (clause Whole_Prop || clause Subterm)

val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>aoa_notice_goal\<close>
      (Args.context -- Scan.lift Parse.embedded -- clauses >>
        (fn ((ctxt, text), clauses) =>
          let
            val patterns = flat clauses
            val _ = List.app (check_pattern ctxt) patterns
            val hint = {serial = serial (), text = text}
          in Thm.declaration_attribute (K (fold (add_pattern hint) patterns)) end))
      "register an AoA notice shown when a goal's conclusion matches a pattern")

end

(*TEMPORARY hunt marker (`exception Option`, 2026-09-03): forces this session to
  rebuild so its ROOT ML_debugger option takes effect (a ROOT options change alone
  does not enter the session digest).  Delete with the hunt.*)
