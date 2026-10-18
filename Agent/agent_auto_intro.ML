(*  Title:      Agent/agent_auto_intro.ML

The automatic Intro decision (IsaMini/AoA/docs/AUTO_INTRO_DECISION.md):
whether AoA inserts its automatic Intro on a state's leading goal.  Once
`Minilang.need_intro` holds, three layers are asked in order: the auto-Intro
hooks, ML functions each giving a verdict or passing; the auto-Intro
exemptions of the Agent Hint Registry, a matching pattern being the verdict
No_Intro; the default, Intro.  Every hook is asked before every exemption,
whatever the scope of each (section 2), so a hook's Intro overrides the
No_Intro a hook asked after it, or an exemption, would give.
*)

signature AUTO_INTRO =
sig
  datatype verdict = Intro | No_Intro
  type hook = Proof.context -> term -> verdict option
    (*a hook's answer on a leading goal, the term Minilang.leading_goal_data
      gives, in the state's context; NONE passes to the next hook; an
      exception propagates*)
  val add_hook : string * hook -> Context.generic -> Context.generic
    (*declares a hook under a name, which `hooks` lists; along one line of
      declarations the most recently declared is asked first, a proof
      context's own before its theory's; at a theory merge a later import's
      first (Library.merge), the serial being the identity*)
  val hooks : Proof.context -> (string * hook) list      (*in the order asked*)
  val verdict_of : Proof.context -> term -> verdict
    (*the first verdict of the three layers: the hooks in order, then the
      exemptions, then Intro*)
  val decide : Minilang.state -> bool
    (*the decision: a leading goal, Minilang.need_intro on the leading
      sequent, and verdict_of is Intro*)
end

structure Auto_Intro : AUTO_INTRO =
struct

datatype verdict = Intro | No_Intro
type hook = Proof.context -> term -> verdict option

(*most recent first along one line of declarations; at a theory merge a later
  import's hooks first; the serial is only the identity*)
structure Hooks = Generic_Data(
  type T = (serial * (string * hook)) list
  val empty = []
  val merge = Library.merge (eq_fst op =))

fun add_hook named = Hooks.map (cons (serial (), named))

fun hooks ctxt = map #2 (Hooks.get (Context.Proof ctxt))

fun verdict_of ctxt goal =
  (case get_first (fn (_, hook) => hook ctxt goal) (hooks ctxt) of
    SOME verdict => verdict
  | NONE => if Agent_Hint.exempt_from_auto_intro ctxt goal then No_Intro else Intro)

fun decide s =
  (case Minilang.leading_goal_data s of
    (NONE, _) => false
  | (SOME (_, goal), _) =>
      Minilang.need_intro (Minilang.leading_proof_sequent_of s)
      andalso verdict_of (Minilang.context_of s) goal = Intro)

end
