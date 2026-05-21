theory Uncheck_Experiment
  imports Main
begin

ML \<open>
fun compact_typ (Type("fun", [A, B])) =
      let val lhs = (case A of Type("fun", _) => "(" ^ compact_typ A ^ ")" | _ => compact_typ A)
      in lhs ^ " \<Rightarrow> " ^ compact_typ B end
  | compact_typ (Type(name, [])) = Long_Name.base_name name
  | compact_typ (Type(name, args)) =
      "(" ^ commas (map compact_typ args) ^ ") " ^ Long_Name.base_name name
  | compact_typ (TFree(a, _)) = a
  | compact_typ (TVar((a, i), _)) =
      if i = 0 then "?" ^ a else "?" ^ a ^ "." ^ string_of_int i

(* Resolve bound variable index to name from enclosing lambdas *)
fun resolve_bound env i =
  if i < length env then nth env i else "?b" ^ string_of_int i

(* Try to evaluate numeral terms to integer *)
fun try_dest_numeral t =
  try HOLogic.dest_number t
  |> Option.map snd

(* Collect head and arguments of curried application *)
fun strip_app (f $ x) = let val (head, args) = strip_app f in (head, args @ [x]) end
  | strip_app t = (t, [])

fun compact_term env (t as Const(name, T)) =
      (case try_dest_numeral t of
        SOME n => string_of_int n
      | NONE => Long_Name.base_name name ^ "[" ^ compact_typ T ^ "]")
  | compact_term env (Free(name, T)) = name ^ "[" ^ compact_typ T ^ "]"
  | compact_term env (Var((name, i), T)) =
      (if i = 0 then "?" ^ name else "?" ^ name ^ "." ^ string_of_int i)
      ^ "[" ^ compact_typ T ^ "]"
  | compact_term env (Bound i) = resolve_bound env i
  | compact_term env (Abs(name, T, body)) =
      "(\<lambda>" ^ name ^ "::" ^ compact_typ T ^ ". " ^ compact_term (name :: env) body ^ ")"
  | compact_term env (t as _ $ _) =
      let val (head, args) = strip_app t
      in
        (* Special case: if head is a numeral-building constant, try evaluating *)
        case try_dest_numeral t of
          SOME n => string_of_int n
        | NONE =>
          let val head_s = compact_term env head
              val args_s = map (fn a =>
                case a of
                  _ $ _ => "(" ^ compact_term env a ^ ")"
                | Abs _ => compact_term env a  (* already parenthesized *)
                | _ => compact_term env a) args
          in head_s ^ " " ^ space_implode " " args_s end
      end
\<close>

text \<open>Test 1: simple locale\<close>

locale my_locale =
  fixes y :: nat
begin

definition f :: "nat \<Rightarrow> nat" where
  "f x = y + x"

ML \<open>
  let
    val ctxt = \<^context>
    val term = Syntax.read_term ctxt "f x"
    val [unchecked] = Syntax.uncheck_terms ctxt [term]
  in
    writeln "--- f x (checked) ---";
    writeln (compact_term [] term);
    writeln "--- f x (unchecked) ---";
    writeln (compact_term [] unchecked)
  end
\<close>

end

text \<open>Test 2: complex expression with multiple constants\<close>

ML \<open>
  let
    val ctxt = \<^context>
    val term = Syntax.read_term ctxt "map Suc (filter (\<lambda>x. x > 0) [1,2,3::nat])"
    val [unchecked] = Syntax.uncheck_terms ctxt [term]
  in
    writeln "--- map/filter (checked) ---";
    writeln (compact_term [] term);
    writeln "--- map/filter (unchecked) ---";
    writeln (compact_term [] unchecked)
  end
\<close>

text \<open>Test 3: quantifiers and connectives\<close>

ML \<open>
  let
    val ctxt = \<^context>
    val term = Syntax.read_term ctxt "\<forall>x::nat. \<exists>y. x + y = 0"
    val [unchecked] = Syntax.uncheck_terms ctxt [term]
  in
    writeln "--- quantifiers (checked) ---";
    writeln (compact_term [] term);
    writeln "--- quantifiers (unchecked) ---";
    writeln (compact_term [] unchecked)
  end
\<close>

text \<open>Test 4: set comprehension\<close>

ML \<open>
  let
    val ctxt = \<^context>
    val term = Syntax.read_term ctxt "{x::nat. x \<in> S \<and> x > 0}"
    val [unchecked] = Syntax.uncheck_terms ctxt [term]
  in
    writeln "--- set comprehension (checked) ---";
    writeln (compact_term [] term);
    writeln "--- set comprehension (unchecked) ---";
    writeln (compact_term [] unchecked)
  end
\<close>

text \<open>Test 5: let binding and case\<close>

ML \<open>
  let
    val ctxt = \<^context>
    val term = Syntax.read_term ctxt "let a = Suc 0 in case a of 0 \<Rightarrow> True | Suc n \<Rightarrow> False"
    val [unchecked] = Syntax.uncheck_terms ctxt [term]
  in
    writeln "--- let/case (checked) ---";
    writeln (compact_term [] term);
    writeln "--- let/case (unchecked) ---";
    writeln (compact_term [] unchecked)
  end
\<close>

end
