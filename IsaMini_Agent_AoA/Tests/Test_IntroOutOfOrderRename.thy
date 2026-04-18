theory Test_IntroOutOfOrderRename
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IntroOutOfOrderRename"]]

(* Goal's internal names are n (first) and m (second).
   We provide variable_bindings=["m"] — one binding only.
   Positional semantics: "m" attaches to the first var (n), renaming it m.
   Keyed semantics:      "m" matches the second var (m); first gets auto-name. *)
lemma t_rename: "\<forall>(n::nat) (m::nat). n + m = m + n"
  by aoa

end
