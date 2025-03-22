### DONE

#### Elaboration

- distinguish for each subgoal the tactics and proofs applied to it.
- normalize all `induct` to `induction`, distinguishing IH and usual hyps

#### Simplification

- unifying various ways of expressing the same thing.
    - unifying `including` and `include`
    - using aaa unfolding bbb -> apply (unfold bbb) using aaa[unfolded bbb]
- simpler (outter) syntax
    - Isar state machine has 3 modes.
- simplify logic
    - When most of other mainstream PAs have only one layer in their logic,
      Isabelle has 2 levels.
      Isabelle is a logic framework, introducing 2 layers in the logic,
      the Meta level that resembles a first-order Pure Type System (PTS);
      and the Object level where the Higher Order Logic is encoded.
    - When other PAs have 2 layers in their proof mode.
      Worse, proof states involve 3 levels.
        Object level, PTS-meta level, PA-meta level (Proof Assistant level)
      An assumption can be represented in either of the 3 levels each of which
      needs quite different ways to handle in the use of the proof assistant.

auto recognize the usage of rules (intro, elim, or dest)

#### 

### TODO

#### Clarification

- goal-directed step-wise calculation
- abductive rearranging lemmas.

#### Elaboration

- parse the explicit rule used in case analysis and induction.

### Nice Examples

- `MS_Test_Sublist.subseq_append`



### tactics to note

rule_tac x="Q' Z" in exI
erule_tac x=s in allE
line 394 in /home/xero/repo/afp-2023-10-16/thys/Simpl/HoarePartialDef.thy


### Notes

using xxx by auto or by (auto simp: xxx)

during the refinement phase, using Sledgehammer to fix proofs.


rev_bexI


lemma assumes wf: "wf_J_prog P"
shows red_preserves_defass:
  "P ⊢ ⟨e,(h,l,sh),b⟩ → ⟨e',(h',l',sh'),b'⟩ ⟹ 𝒟 e ⌊dom l⌋ ⟹ 𝒟 e' ⌊dom l'⌋"
and "P ⊢ ⟨es,(h,l,sh),b⟩ [→] ⟨es',(h',l',sh'),b'⟩ ⟹ 𝒟s es ⌊dom l⌋ ⟹ 𝒟s es' ⌊dom l'⌋"

INDUCT rule:red_reds_inducts
NEXT WITH RedNew
NEXT WITH RedNewFail
NEXT WITH NewInitDoneRed
NEXT WITH NewInitRed
NEXT WITH CastRed
NEXT WITH RedCastNull
NEXT WITH RedCast
NEXT WITH RedCastFail
NEXT WITH BinOpRed1
NEXT WITH BinOpRed2
NEXT WITH RedBinOp
NEXT WITH RedVar
NEXT WITH LAssRed
NEXT WITH RedLAss
NEXT WITH FAccRed
NEXT WITH RedFAcc
NEXT WITH RedFAccNull
NEXT WITH RedFAccNone
NEXT WITH RedFAccStatic
NEXT WITH RedSFAcc
NEXT WITH SFAccInitDoneRed
NEXT WITH SFAccInitRed
NEXT WITH RedSFAccNone
NEXT WITH RedSFAccNonStatic
NEXT WITH FAssRed1
NEXT WITH FAssRed2
NEXT WITH RedFAss
NEXT WITH RedFAssNull
NEXT WITH RedFAssNone
NEXT WITH RedFAssStatic
NEXT WITH SFAssRed
NEXT WITH RedSFAss
NEXT WITH SFAssInitDoneRed
NEXT WITH SFAssInitRed
NEXT WITH RedSFAssNone
NEXT WITH RedSFAssNonStatic
NEXT WITH CallObj
NEXT WITH CallParams
  APPLY (auto dest!:sees_wf_mdecl[OF wf] simp:wf_mdecl_def hyperset_defs elim!:D_mono') WITH RedCall
NEXT
NEXT WITH RedCallNull
NEXT WITH RedCallNone hyperset_defs
NEXT WITH RedCallStatic
NEXT WITH SCallParams hyperset_defs
  APPLY (auto dest!:sees_wf_mdecl[OF wf] simp:wf_mdecl_def hyperset_defs elim!:D_mono') WITH RedSCall
NEXT
NEXT WITH hyperset_defs(1,2,3,4) SCallInitDoneRed
NEXT WITH hyperset_defs(1,2,3,4) SCallInitRed
NEXT WITH hyperset_defs(1,2,3,4) RedSCallNone
NEXT WITH hyperset_defs(1,2,3,4) RedSCallNonStatic
NEXT WITH Diff_empty dom_minus BlockRedNone WITHOUT fun_upd_apply
NEXT WITH BlockRedSome WITHOUT fun_upd_apply
NEXT WITH InitBlockRed WITHOUT fun_upd_apply
NEXT WITH hyperset_defs(1,2,3,4) RedBlock
NEXT WITH hyperset_defs(1,2,3,4) RedInitBlock
NEXT WITH SeqRed
NEXT WITH hyperset_defs(1,2,3,4) RedSeq
NEXT WITH D_mono[OF red_lA_incr] CondRed
NEXT WITH hyperset_defs(1,2,3,4) RedCondT
NEXT WITH hyperset_defs(1,2,3,4) RedCondF
  APPLY (auto simp:hyperset_defs elim!:D_mono') WITH RedWhile
NEXT
NEXT WITH hyperset_defs(1,2,3,4) ThrowRed
NEXT WITH hyperset_defs(1,2,3,4) RedThrowNull
NEXT WITH TryRed
NEXT WITH hyperset_defs(1,2,3,4) RedTry
NEXT WITH hyperset_defs(1,2,3,4) RedTryCatch
NEXT WITH hyperset_defs(1,2,3,4) RedTryFail
NEXT WITH ListRed1
NEXT WITH hyperset_defs(1,2,3,4) ListRed2
NEXT WITH hyperset_defs(1,2,3,4) RedInit
NEXT WITH hyperset_defs(1,2,3,4) InitNoneRed
NEXT WITH hyperset_defs(1,2,3,4) RedInitDone
NEXT WITH hyperset_defs(1,2,3,4) RedInitProcessing
NEXT WITH hyperset_defs(1,2,3,4) RedInitError
NEXT WITH hyperset_defs(1,2,3,4) InitObjectRed
NEXT WITH hyperset_defs(1,2,3,4) InitNonObjectSuperRed
NEXT VARS e h l sh b e' h' l' sh' b' C Cs e⇩0 WITH hyperset_defs(1,2,3,4) RedInitRInit
NEXT WITH RInitRed
NEXT WITH hyperset_defs(1,2,3,4) RedRInit
NEXT WITH hyperset_defs(1,2,3,4) CastThrow
NEXT WITH hyperset_defs(1,2,3,4) BinOpThrow1
NEXT WITH hyperset_defs(1,2,3,4) BinOpThrow2
NEXT WITH hyperset_defs(1,2,3,4) LAssThrow
NEXT WITH hyperset_defs(1,2,3,4) FAccThrow
NEXT WITH hyperset_defs(1,2,3,4) FAssThrow1
NEXT WITH hyperset_defs(1,2,3,4) FAssThrow2
NEXT WITH hyperset_defs(1,2,3,4) SFAssThrow
NEXT WITH hyperset_defs(1,2,3,4) CallThrowObj
NEXT WITH hyperset_defs(1,2,3,4) CallThrowParams
NEXT WITH hyperset_defs(1,2,3,4) SCallThrowParams
NEXT WITH hyperset_defs(1,2,3,4) BlockThrow
NEXT WITH hyperset_defs(1,2,3,4) InitBlockThrow
NEXT WITH hyperset_defs(1,2,3,4) SeqThrow
NEXT WITH hyperset_defs(1,2,3,4) CondThrow
NEXT WITH hyperset_defs(1,2,3,4) ThrowThrow
NEXT WITH hyperset_defs(1,2,3,4) RInitInitThrow
END WITH hyperset_defs(1,2,3,4) RInitThrow





Comment: ignore (* *), preserve --<comment>
