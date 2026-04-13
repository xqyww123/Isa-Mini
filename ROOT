
session Minilang = Auto_Sledgehammer +
  theories
    Minilang_Base
    Minilang

session Minilang_Test in Test = Minilang +
  theories
    Fun_In_Proof_Test

session Minilang_Translator in translator = Minilang +
  sessions
    Isa_REPL
  theories
    MS_Translator
    MS_Translator_Top

session Minilang_REPL in REPL = Minilang +
  sessions
    Isa_REPL
  theories
    Minilang_Top

session Minilang_Agent in Agent = Minilang +
  sessions
    Isa_REPL
    Isabelle_RPC
    Semantic_Embedding
  theories
    Minilang_Agent
