theory Test_sqrt2
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin
declare [[auto_interpret_for_embedding=false, agent_AoA_driver="ChatGPT.gpt-5.5-high"]]

theorem sqrt2_not_rational:
    "sqrt 2 \<notin> \<rat>"
  by aoa


end