### Isabelle version upgrade checklist

When upgrading the bundled Isabelle (currently **Isabelle2024**), the
following pieces of `library/proof.ML` were forked/replicated from
Isabelle internals and MUST be resynced:

- **Rule-pick helpers** (lookup: `ISABELLE VERSION SYNC REQUIRED ON UPGRADE`
  block comment in `proof.ML`):
  - `ind_align_left` / `ind_align_right` — from `induct.ML:401-407`
  - `ind_prep_inst` — from `induct.ML:412`
  - `ind_special_rename_params` — from `induct.ML:633`
  - `ind_get_inductP` — from `induct.ML:754`
  - `ind_get_casesT` / `ind_get_casesP` — from `induct.ML:485-489`
  - `mk_induct_inst_rule` — from the `inst_rule` local in
    `gen_induct_context_tactic` (`induct.ML:763`)
  - `mk_cases_inst_rule` — from the `inst_rule` local in
    `cases_context_tactic` (`induct.ML:496`)
- **Dependencies**: `Rule_Cases.get_consumes`, `Rule_Cases.get`,
  `Rule_Cases.consume`, `Rule_Cases.strict_mutual_rule`,
  `Rule_Cases.mutual_rule` (in `rule_cases.ML`).

Symptoms of missed sync: `analyze_induct` / `analyze_case_split`
reports a stale rule; consume-fact validation fires on the wrong rule;
subtle divergence between analysis and execution of `INDUCT`/`CASE_SPLIT`.

To resync, diff the referenced source regions against the fork and
re-apply any semantic changes.

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

#### Agent

- SIMPLIFY\_GOAL\_AND\_PREMISES' (`proof.ML`): `clarsimp_tac` always succeeds even with no progress (no `CHANGED_PROP` wrapper). A no-op Rewrite silently succeeds instead of raising `OPR_FAIL`. Consider wrapping with `CHANGED_PROP` to detect and report no-progress cases.

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


### Missing Theories for MathBench_Prover (Trigonometric Analysis)

Identified from putnam_2000_b3 evaluation. All items are missing from both Isabelle/HOL
and the AFP (confirmed through AFP mid-2026). Items 1-3 are undergraduate-level facts;
items 4-6 are standard graduate analysis used broadly in PDE, harmonic analysis,
approximation theory.

#### Easy (< 50 lines each, straightforward induction)

1. **`higher_deriv_sin`**: `(deriv ^^ k) sin z = sin(z + of_nat k * (pi/2))`
   - Strategy: induction on k using DERIV_sin/DERIV_cos + cos x = sin(x + pi/2)
   - Deps: Transcendental.thy (DERIV_sin, sin_add)

2. **`higher_deriv_sin_scaled`**: `(deriv ^^ k)(λt. sin(c*t)) t = c^k * sin(c*t + k*π/2)`
   - Strategy: instantiate higher_deriv_compose_linear' (Complex_Analysis) + item 1
   - Deps: item 1, Cauchy_Integral_Formula.thy (higher_deriv_compose_linear')

#### Medium (40-70 lines, smoothness assumptions threading)

3. **`higher_deriv_sum_real`**: `(deriv ^^ k)(λt. ∑j∈S. f j t) t = ∑j∈S. (deriv ^^ k)(f j) t`
   - Strategy: induction on k using deriv_sum; or lift from higher_deriv_add (complex)
   - Deps: Derivative.thy (deriv_sum), or Cauchy_Integral_Formula.thy (higher_deriv_add)
   - Note: real version requires explicit k-differentiability assumption

#### Hard (150-250 lines, algebraic reduction)

4. **`trig_poly_finite_zeros`**: non-zero trig poly of degree N has ≤ 2N zeros on [0,1)
   - Strategy: reduce to algebraic poly via Chebyshev (sin(jx) = sin(x)*U_{j-1}(cos x))
     or via Laurent poly in z = e^{2πit}; then apply card_poly_roots_bound
   - Deps: AFP Chebyshev_Polynomials (cheb_poly_cos, cheb_poly'_cos),
     Polynomial.thy (card_poly_roots_bound)
   - Note: AFP Budan_Fourier.Sturm_Multiple_Roots may also help (parallel to Budan_Fourier)

#### Hard-to-Very-Hard (400-800 lines, complex analysis reduction)

5. **`bernstein_inequality_trig`**: if f(x) = Σ_{k=0}^{n} (aₖ sin(kx) + bₖ cos(kx))
   and |f(x)| ≤ 1 for all x, then |f'(x)| ≤ n. Stronger form: |f'(x)|² ≤ n²(1 - f(x)²).
   - Strategy (recommended): complex analysis via maximum modulus principle.
     (a) Convert trig poly to Laurent poly g(z) = Σ cₖ zᵏ on unit circle via z = e^{ix};
     (b) Apply `maximum_modulus_principle` (HOL-Complex_Analysis/Conformal_Mappings.thy);
     (c) Relate |g'(z)| bound to |f'(x)| bound via Cauchy integral formula.
   - Alternative: Fourier approach via Parseval (available in AFP/Fourier), but needs
     L²→L∞ norm bounds not currently formalized.
   - Deps: HOL-Complex_Analysis (`maximum_modulus_principle`, `holomorphic_on`,
     Cauchy integral formula), `cis` / Euler formula (Transcendental.thy)
   - Identified from putnam_1962_b6 evaluation.

#### Very Hard (500-700 lines each, AFP-contribution-scale)

6. **`circular_Rolle`**: if f continuous on [a,b], differentiable on (a,b), f(a)=f(b),
   f has n zeros (counting multiplicity) on [a,b), then f' has ≥ n zeros on [a,b)
   - Strategy: combine multiplicity-reduction (order m zero → order m-1 for f') with
     standard Rolle between consecutive zeros + wrap-around from f(a)=f(b)
   - Blocker: NO existing "zero multiplicity" for general smooth functions in Isabelle
     (only for polynomials via `order` in Polynomial.thy). Must define vanishing order
     and prove basic properties.
   - Deps: Deriv.thy (Rolle_deriv), Taylor's theorem (HOL-Analysis)

7. **`trig_poly_deriv_zero_limit`**: for f(t) = ∑_{j=1}^N a_j sin(2πjt) with a_N ≠ 0,
   the zero count of f^(k) on [0,1) converges to 2N as k→∞
   - Strategy: upper bound from item 4; lower bound via asymptotic domination of
     a_N(2πN)^k sin(2πNt + kπ/2) (since (j/N)^k → 0 for j<N), then Hurwitz-type
     perturbation argument (zeros of uniform limit persist)
   - Blocker: NO Hurwitz theorem for real functions in Isabelle. Complex version exists
     but doesn't directly transfer.
   - Deps: items 2, 3, 4, (partially 6 for multiplicity)

#### Dependency graph

```
1. higher_deriv_sin            (standalone)
2. higher_deriv_sin_scaled     ──── depends on ──→ 1
3. higher_deriv_sum_real       (standalone)
4. trig_poly_finite_zeros      (standalone; needs AFP Chebyshev_Polynomials)
5. bernstein_inequality_trig   (standalone; needs HOL-Complex_Analysis)
6. circular_Rolle              (standalone; new infrastructure)
7. trig_poly_deriv_zero_limit  ──── depends on ──→ 2, 3, 4, (partially 6)
```

#### Imports needed in MathBench_Prover

Currently NOT imported but contain relevant building blocks:
- `HOL-Complex_Analysis.Complex_Analysis` — higher_deriv_add, higher_deriv_compose_linear'
- `Chebyshev_Polynomials.Chebyshev_Polynomials` — cheb_poly_cos, sin/cos multiple angle
- `Budan_Fourier.Budan_Fourier` / `Budan_Fourier.Sturm_Multiple_Roots` — proots_count
- `Fourier.Fourier` — periodic function infrastructure (heavy: depends on HOL-Probability)

---

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
