theory Minilang_AoA_App
  imports Minilang_AoA.Minilang_AoA Isa_REPL.Isa_REPL
begin

(* Registers the "Minilang.AoA" REPL-server app. This lives in its own session
   (Minilang_AoA_REPL = Minilang_AoA + Isa_REPL) so that Minilang_AoA itself
   stays free of Isa_REPL. Clients that drive AoA over the REPL app load THIS
   theory (add_lib "Minilang_AoA_REPL.Minilang_AoA_App"); `by aoa` users import
   plain Minilang_AoA. *)
ML_file \<open>aoa_repl_app.ML\<close>

end
