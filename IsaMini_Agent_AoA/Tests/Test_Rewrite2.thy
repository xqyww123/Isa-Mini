theory Test_Rewrite2
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite2"]]
  
(* Test rewriting premises with equations *)
lemma rewrite_test:
  assumes h1: "y = x + 0"
      and h2: "\<exists>aAa. z = y * 1 + aAa"
  shows "x = z \<and> PP z \<and> (\<forall>x. AA z x)"
  by      aoa 


end
