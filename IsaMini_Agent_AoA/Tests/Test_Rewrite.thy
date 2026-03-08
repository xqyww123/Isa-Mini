theory Test_Rewrite
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite"]]
  
(* Test rewriting premises with equations *)
lemma rewrite_test:
  assumes h1: "y = x + 0"
      and h2: "\<exists>a. z = y * 1 + a"
  shows "x = z"
  by   AgentAoA 


end
