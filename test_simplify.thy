theory test_simplify
  imports Minilang_Agent.Minilang_Agent
begin

section \<open>Test Cases for SIMPLIFY operation\<close>

(* Test 1: Basic case - conjunction in premise should split *)
lemma test1:
  assumes ab: "A ∧ B"
  shows "C"
  apply (min_script \<open>
    SIMPLIFY PREMISES ab
  \<close>)
  (* Expected: assm1: A, assm2: B, goal: C *)
  oops

(* Test 2: No change - premises already simplified *)
lemma test2:
  assumes a: "A"
      and b: "B"
  shows "C"
  apply (min_script \<open>
    SIMPLIFY PREMISES a and b
  \<close>)
  (* Expected: no new facts (both unchanged), goal: C *)
  oops

(* Test 3: Partial change - one premise changes, one doesn't *)
lemma test3:
  assumes ab: "A ∧ B"
      and c: "C"
  shows "D"
  apply (min_script \<open>
    SIMPLIFY PREMISES ab and c
  \<close>)
  (* Expected: assm1: A, assm2: B (from ab), c unchanged, goal: D *)
  oops

(* Test 4: Nested conjunctions *)
lemma test4:
  assumes abc: "(A ∧ B) ∧ C"
  shows "D"
  apply (min_script \<open>
    SIMPLIFY PREMISES abc
  \<close>)
  (* Expected: assm1: A, assm2: B, assm3: C, goal: D *)
  oops

(* Test 5: Multiple premises with conjunctions *)
lemma test5:
  assumes ab: "\<forall> x. A ∧ B"
      and cd: "C ∧ D"
  shows "E"
  apply (min_script \<open>
    SIMPLIFY PREMISES ab and cd
  \<close>)
  (* Expected: assm1: A, assm2: B, assm3: C, assm4: D, goal: E *)
  oops

(* Test 6: Conjunction in goal (if simplify_goal = false, should not change) *)
lemma test6:
  assumes a: "A"
  shows "B ∧ C"
  apply (min_script \<open>
    SIMPLIFY PREMISES a
  \<close>)
  (* Expected: a unchanged, goal: B ∧ C (not split because of NO_SIMP protection) *)
  oops

(* Test 7: Empty premise list - only goal *)
(* This should fail - no premises to simplify *)
(* lemma test7:
  shows "A ⟶ B"
  apply (min_script \<open>
    SIMPLIFY PREMISES
  \<close>)
  oops *)

(* Test 8: Implication in premise (should be handled by clarsimp) *)
lemma test8:
  assumes ab: "A ⟶ B"
      and a: "A"
  shows "C"
  apply (min_script \<open>
    SIMPLIFY PREMISES ab and a
  \<close>)
  (* Expected: depends on clarsimp behavior, might derive B *)
  oops

(* Test 9: Disjunction in premise *)
lemma test9:
  assumes ab: "A ∨ B"
  shows "C"
  apply (min_script \<open>
    SIMPLIFY PREMISES ab
  \<close>)
  (* Expected: clarsimp might not split disjunction, so ab might remain unchanged *)
  oops

(* Test 10: Using WITH clause for additional simplification rules *)
lemma test10:
  assumes pt: "P ∧ True"
  shows "Q"
  apply (min_script \<open>
    SIMPLIFY PREMISES pt
  \<close>)
  (* Expected: assm1: P (True eliminated), goal: Q *)
  oops

(* Test 11: Triple conjunction *)
lemma test11:
  assumes abc: "A ∧ B ∧ C"
  shows "D"
  apply (min_script \<open>
    SIMPLIFY PREMISES abc
  \<close>)
  (* Expected: assm1: A, assm2: B, assm3: C, goal: D *)
  oops

(* Test 12: All premises unchanged *)
lemma test12:
  assumes p: "P"
      and q: "Q"
      and r: "R"
  shows "S"
  apply (min_script \<open>
    SIMPLIFY PREMISES p and q and r
  \<close>)
  (* Expected: no new facts, goal: S *)
  oops

(* Test 13: Mix of changed and unchanged with multiple conjunctions *)
lemma test13:
  assumes ab: "A ∧ B"
      and c: "C"
      and de: "D ∧ E"
      and f: "F"
  shows "G"
  apply (min_script \<open>
    SIMPLIFY PREMISES ab and c and de and f
  \<close>)
  (* Expected: assm1: A, assm2: B, assm3: D, assm4: E; c and f unchanged *)
  oops

end
