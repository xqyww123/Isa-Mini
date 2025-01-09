
session Minilang = HOL +
  theories
    Minilang_Base
    Minilang

session Minilang_Translator in Translator = Minilang +
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