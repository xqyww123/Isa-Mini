(*  Title:      Isa-Mini/library/function/proof_local_lthy.ML
    Author:     Qiyuan Xu (with AI assistance)

Proof-local replacements for Local_Theory operations.
These use Local_Defs and Proof_Context operations that do NOT modify
the background theory, allowing recursive function definitions
inside proof blocks without forking the theory.

Result-discharge timing: Proof_Local_Lthy.define uses Local_Defs.define,
which adds its definition as an assumption (Free(b) \<equiv> rhs) to the proof
context. The assumption must be discharged by Proof_Context.export at a
scope boundary — see the header of proof_local_function.ML for the full
timing-requirement discussion.
*)

signature PROOF_LOCAL_LTHY =
sig
  (* drop-in replacement for Local_Theory.define *)
  val define: (binding * mixfix) * (Attrib.binding * term) ->
    Proof.context -> (term * (string * thm)) * Proof.context

  (* drop-in replacement for Local_Theory.note *)
  val note: Attrib.binding * thm list ->
    Proof.context -> (string * thm list) * Proof.context

  (* drop-in replacement for Local_Theory.notes *)
  val notes: Attrib.fact list ->
    Proof.context -> (string * thm list) list * Proof.context

  (* drop-in replacement for Local_Theory.notes with kind *)
  val notes_kind: string -> Attrib.fact list ->
    Proof.context -> (string * thm list) list * Proof.context

  (* drop-in for Local_Theory.declaration — no-op *)
  val declaration: {syntax: bool, pervasive: bool, pos: Position.T} ->
    Morphism.declaration -> Proof.context -> Proof.context
end

structure Proof_Local_Lthy : PROOF_LOCAL_LTHY =
struct

(* Local define using Local_Defs.define.
   Returns (lhs, (def_name, def_thm)) like Local_Theory.define,
   but without modifying the background theory.
   Attrib.binding = binding * Token.src list; we extract just the binding
   for Local_Defs.define which takes plain binding. *)
fun define ((b, mx), ((b_def, raw_atts) : Attrib.binding, rhs)) ctxt =
  let
    val atts = map (Attrib.attribute ctxt) raw_atts
    val ([(lhs, (name, th))], ctxt') =
      Local_Defs.define [((b, mx), ((b_def, atts), rhs))] ctxt
  in ((lhs, (name, th)), ctxt') end

(* Local note using Attrib.local_notes.
   Attrib.binding = binding * Token.src list (raw attributes). *)
fun notes_kind kind facts ctxt =
  Attrib.local_notes kind facts ctxt

fun notes facts ctxt = notes_kind "" facts ctxt

fun note (b, ths) ctxt =
  let val ([(name, noted)], ctxt') = notes [((b, [(ths, [])]))] ctxt
  in ((name, noted), ctxt') end

(* Declaration — no-op in proof context *)
fun declaration _ _ ctxt = ctxt

end
