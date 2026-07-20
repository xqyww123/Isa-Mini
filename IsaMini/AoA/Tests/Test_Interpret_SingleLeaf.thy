theory Test_Interpret_SingleLeaf
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Interpret_SingleLeaf"]]

(* N = 1 leaf -- the critical corner case. The default SubgoalMaker rule only
   opens a block when the operation reports MORE THAN ONE new subgoal; with a
   single-assumption locale exactly one leaf is reported, so if
   `Interpret_Locale._should_open_proof_block` were not unconditional, no END
   would be emitted, the ML block would never close, and the interpretation
   would never register. *)

locale is1_pos = fixes p :: nat assumes is1_bp: "p > 0"
begin
lemma is1_dbl_pos: "p + p > 0" using is1_bp by simp
end

lemma "(0::nat) < 3 + 3"
  by aoa

end
