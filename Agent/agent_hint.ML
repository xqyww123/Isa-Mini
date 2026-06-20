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

(* Fire one registered hit. *)
fun fire (_, (Reject, text)) =
      raise Minilang.OPR_FAIL (Minilang.TERMLANG, text)
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
   never create a `"??.unknown"` key. Used by the `agent_notice`/`agent_reject`
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

(* Declaration attributes:
     declare [[agent_notice_constant <const> "..."]]
     declare [[agent_reject_constant <const> "..."]]
     declare <fact> [agent_notice "..."]
     declare <fact> [agent_reject "..."]
   The constant attributes follow the `coercion`/`coercion_args` idiom
   (`Args.const` resolves to the fully-qualified name at declaration time, so
   matching is immune to short-name/ambiguity); they ignore the (empty) fact.
   The fact attributes key on `Thm.get_name_hint`. *)
val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>agent_notice_constant\<close>
      (Args.const {proper = true, strict = false} -- Scan.lift Parse.embedded >>
        (fn (c, text) => Thm.declaration_attribute (K (add_const (c, (Notice, text))))))
      "register an agent NOTICE hint on a constant the agent should avoid" #>
    Attrib.setup \<^binding>\<open>agent_reject_constant\<close>
      (Args.const {proper = true, strict = false} -- Scan.lift Parse.embedded >>
        (fn (c, text) => Thm.declaration_attribute (K (add_const (c, (Reject, text))))))
      "register an agent REJECT hint on a constant the agent must not use" #>
    Attrib.setup \<^binding>\<open>agent_notice\<close>
      (Scan.lift Parse.embedded >>
        (fn text => Thm.declaration_attribute (add_fact_hint Notice text)))
      "register an agent NOTICE hint on a fact the agent should avoid" #>
    Attrib.setup \<^binding>\<open>agent_reject\<close>
      (Scan.lift Parse.embedded >>
        (fn text => Thm.declaration_attribute (add_fact_hint Reject text)))
      "register an agent REJECT hint on a fact the agent must not use")

end
