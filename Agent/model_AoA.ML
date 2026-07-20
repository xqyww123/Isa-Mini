(**** Minilang AoA -- Agent over AST ****)
structure MiniLang_Agent_AoA = struct

type icmd = MiniLang_Agent.icmd
datatype proof_tree = Node of {
  id: string,
  thought: string,
  cmd: icmd,
  subs: proof_tree list
}

end