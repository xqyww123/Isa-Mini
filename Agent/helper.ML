signature MINILANG_HELPER = sig

val guess_default_num_typ : term -> typ option

end

structure Minilang_Helper : MINILANG_HELPER = struct

fun guess_default_num_typ prop =
  if exists_type (exists_subtype (fn Type (\<^type_name>\<open>real\<close>, _) => true | _ => false)) prop
  then SOME \<^typ>\<open>real\<close>
  else if exists_type (exists_subtype (fn Type (\<^type_name>\<open>int\<close>, _) => true | _ => false)) prop
  then SOME \<^typ>\<open>int\<close>
  else if exists_type (exists_subtype (fn Type (\<^type_name>\<open>nat\<close>, _) => true | _ => false)) prop
  then SOME \<^typ>\<open>nat\<close>
  else SOME \<^typ>\<open>int\<close>

end
