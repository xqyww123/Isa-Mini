theory Clarsimp_Tac_Test
  imports Main Minilang.Minilang
begin

text \<open>Test whether @{ML Clasimp.clarsimp_tac} always succeeds (even with no progress).
  This matters for the SIMPLIFY operation in proof.ML which calls
  @{ML Clasimp.clarsimp_tac} and takes @{ML Seq.hd} of the result.\<close>

text \<open>Group A: A goal where clarsimp CAN make progress via classical reasoning
  (conjunction splitting + assumption resolution).\<close>

ML \<open>
local
  val ctxt0 = \<^context>
  val goal_ct = \<^cterm>\<open>P (x::nat) \<Longrightarrow> Q (y::nat) \<Longrightarrow> P x \<and> Q y\<close>
  val st = Goal.init goal_ct
  val cleared_ctxt = Simplifier.clear_simpset ctxt0
in
  val _ = writeln ("A1 (clarsimp_tac, cleared simpset, splittable goal): " ^
    string_of_int (length (Clasimp.clarsimp_tac cleared_ctxt 1 st |> Seq.list_of)) ^ " result(s)")
  val _ = writeln ("A2 (CHANGED clarsimp_tac, cleared simpset, splittable goal): " ^
    string_of_int (length (CHANGED (Clasimp.clarsimp_tac cleared_ctxt 1) st |> Seq.list_of)) ^ " result(s)")
end
\<close>

text \<open>Group B: A goal where clarsimp genuinely CANNOT make progress:
  no conjunction to split, no matching premises, cleared simpset.\<close>

ML \<open>
local
  val ctxt0 = \<^context>
  (* R x ==> S y: no classical reasoning can help, no simp rules apply *)
  val goal_ct = \<^cterm>\<open>R (x::nat) \<Longrightarrow> S (y::nat)\<close>
  val st = Goal.init goal_ct
  val cleared_ctxt = Simplifier.clear_simpset ctxt0
in
  val _ = writeln ("B1 (clarsimp_tac, cleared simpset, opaque goal): " ^
    string_of_int (length (Clasimp.clarsimp_tac cleared_ctxt 1 st |> Seq.list_of)) ^ " result(s)")
  val _ = writeln ("B2 (CHANGED clarsimp_tac, cleared simpset, opaque goal): " ^
    string_of_int (length (CHANGED (Clasimp.clarsimp_tac cleared_ctxt 1) st |> Seq.list_of)) ^ " result(s)")
end
\<close>

text \<open>Group C: Same opaque goal but with full simpset.\<close>

ML \<open>
local
  val ctxt0 = \<^context>
  val goal_ct = \<^cterm>\<open>R (x::nat) \<Longrightarrow> S (y::nat)\<close>
  val st = Goal.init goal_ct
in
  val _ = writeln ("C1 (clarsimp_tac, full simpset, opaque goal): " ^
    string_of_int (length (Clasimp.clarsimp_tac ctxt0 1 st |> Seq.list_of)) ^ " result(s)")
  val _ = writeln ("C2 (CHANGED clarsimp_tac, full simpset, opaque goal): " ^
    string_of_int (length (CHANGED (Clasimp.clarsimp_tac ctxt0 1) st |> Seq.list_of)) ^ " result(s)")
end
\<close>

text \<open>Group D: Simulating what SIMPLIFY does \<^bold>\<open>exactly\<close>:
  insert a premise into the goal, then clarsimp with an irrelevant simp rule
  and a cleared simpset. This mirrors the agent Rewrite path.\<close>

ML \<open>
local
  val ctxt0 = \<^context>
  (* Goal: R x ==> S x ==> R x & S x, with premise "R x" inserted *)
  val goal_ct = \<^cterm>\<open>R (x::nat) \<Longrightarrow> S (x::nat) \<Longrightarrow> R x \<and> S x\<close>
  val st0 = Goal.init goal_ct

  (* Step 1: Insert first premise (simulating what SIMPLIFY does for rewrite premises) *)
  val prem_thm = @{thm TrueI} (* irrelevant rule, just to have something *)
  val cleared_ctxt = Simplifier.clear_simpset ctxt0
  (* Use cleared simpset + one irrelevant simp rule *)
  val simp_ctxt = cleared_ctxt addsimps [@{thm TrueI}]

  (* Step 2: Apply clarsimp_tac (this is what proof.ML line 1786 does) *)
in
  val _ = writeln ("D1 (clarsimp_tac, cleared+irrelevant, conjunction goal): " ^
    string_of_int (length (Clasimp.clarsimp_tac simp_ctxt 1 st0 |> Seq.list_of)) ^ " result(s)")
  val _ = writeln ("D2 (CHANGED clarsimp_tac, cleared+irrelevant, conjunction goal): " ^
    string_of_int (length (CHANGED (Clasimp.clarsimp_tac simp_ctxt 1) st0 |> Seq.list_of)) ^ " result(s)")
end
\<close>


text \<open>Group E: The SIMPLIFY path with premise insertion on a truly opaque goal.
  After inserting a premise, does clarsimp with irrelevant rules change anything?\<close>

ML \<open>
local
  val ctxt0 = \<^context>
  val goal_ct = \<^cterm>\<open>R (x::nat) \<Longrightarrow> S (y::nat)\<close>
  val st0 = Goal.init goal_ct

  (* Insert the premise "R x" into the goal *)
  val prem_thms = [Proof_Context.get_thm ctxt0 "Pure.protectI"] handle ERROR _ => []

  val cleared_ctxt = Simplifier.clear_simpset ctxt0
  val simp_ctxt = cleared_ctxt addsimps [@{thm TrueI}]
in
  val _ = writeln ("E1 (clarsimp_tac, cleared+irrelevant, opaque goal): " ^
    string_of_int (length (Clasimp.clarsimp_tac simp_ctxt 1 st0 |> Seq.list_of)) ^ " result(s)")
  val _ = writeln ("E2 (CHANGED clarsimp_tac, cleared+irrelevant, opaque goal): " ^
    string_of_int (length (CHANGED (Clasimp.clarsimp_tac simp_ctxt 1) st0 |> Seq.list_of)) ^ " result(s)")
end
\<close>


text \<open>Group F: min\_script test with SIMPLIFY on a named premise using an irrelevant rule.\<close>

definition \<open>irrelevant \<equiv> (0::nat) = 0\<close>

lemma "P (x::nat) \<Longrightarrow> Q (y::nat) \<Longrightarrow> P x \<and> Q y"
  by (min_script \<open>
    INTRO
    SIMPLIFY PREMISES assm0 WITH irrelevant_def
    END
  \<close>)

text \<open>If the above lemma compiles, the SIMPLIFY with an irrelevant rule succeeded
  without error, confirming that clarsimp\_tac does not fail on no-progress.

  Summary: check the output window for results of groups A\<dash>E.
  Key question: does group B/E show 0 results for CHANGED?\<close>

record point = xcoord :: nat  ycoord :: nat
record cpoint = point + color :: string

ML \<open>case @{typ \<open>cpoint\<close>} of Type (_, [Type x  ]) => x\<close>

term cpoint.make
term cpoint.fields
typ cpoint_ext
typ "unit point_scheme"
typ "unit point_ext"
typ "unit cpoint_scheme"
typ "unit cpoint_ext"
typ 

end
