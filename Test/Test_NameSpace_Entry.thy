theory Test_NameSpace_Entry
  imports Main
begin

text \<open>
  Part 1: empirically determine which component of a theorem's
  @{ML_type Thm_Name.T} name hint @{ML Name_Space.the_entry} expects --- the
  bare fact name (#1) or the printed @{ML Thm_Name.print} form
  @{verbatim \<open>name(index)\<close>}.
\<close>

ML \<open>
local
  val ctxt = @{context};
  val space = Facts.space_of (Proof_Context.facts_of ctxt);

  fun probe label thm =
    let
      val nh = Thm.get_name_hint thm
      val base = #1 nh
      val printed = Thm_Name.print nh
      val base_ok = is_some (try (Name_Space.the_entry space) base)
      val print_ok = is_some (try (Name_Space.the_entry space) printed)
    in
      writeln (label ^ ": name_hint=(\"" ^ base ^ "\"," ^ string_of_int (#2 nh) ^ ")" ^
        "  printed=" ^ printed ^
        "  the_entry[base]=" ^ Bool.toString base_ok ^
        "  the_entry[printed]=" ^ Bool.toString print_ok)
    end;
in
  val _ = probe "conjI" @{thm conjI};
  val _ = map_index (fn (i, th) => probe ("list.distinct#" ^ string_of_int i) th)
            @{thms list.distinct};
  val _ = map_index (fn (i, th) => probe ("list.sel#" ^ string_of_int i) th)
            @{thms list.sel};
end
\<close>

text \<open>
  Part 2: verify the @{ML Thm_Name.print} / \<open>parse_thm_xname\<close> round-trip.
  \<open>parse_thm_xname\<close> is a \<^verbatim>\<open>local\<close> function in Universal_Key.ML, so it
  is mirrored here VERBATIM and exercised as the inverse of @{ML Thm_Name.print}:
    print (name, idx) -> "name" or "name(idx)" -> parse -> (name, idx-or-NONE)
  and the parsed name is resolved back to a theorem whose prop must match.
\<close>

ML \<open>
local
  (* --- verbatim copy of parse_thm_xname from Universal_Key.ML (lines 345-360) --- *)
  fun parse_thm_xname xname =
    let val len = size xname
    in
      if len > 2 andalso String.sub (xname, len - 1) = #")"
      then case Substring.fields (fn c => c = #"(")
                  (Substring.full xname) of
          [base, idx_paren] =>
            let val idx_str = Substring.string
                  (Substring.trimr 1 idx_paren)
            in case Int.fromString idx_str of
                SOME i => (Substring.string base, SOME i)
              | NONE => (xname, NONE)
            end
        | _ => (xname, NONE)
      else (xname, NONE)
    end;

  fun assert msg true = () | assert msg false = error ("FAILED: " ^ msg);

  val ctxt = @{context};
  val gctxt = Context.Proof ctxt;
  val facts = Proof_Context.facts_of ctxt;
  val space = Facts.space_of facts;

  fun roundtrip th =
    let
      val nh = Thm.get_name_hint th
      val printed = Thm_Name.print nh
      val (base, idx_opt) = parse_thm_xname printed
      (* Thm_Name.print emits the "(idx)" suffix only when idx <> 0 (and name <> "") *)
      val expected_idx = if #1 nh = "" orelse #2 nh = 0 then NONE else SOME (#2 nh)
      val _ = assert ("base recovers fact name for " ^ printed) (base = #1 nh)
      val _ = assert ("index recovers for " ^ printed) (idx_opt = expected_idx)
      (* end-to-end: resolve the parsed name back to a theorem, compare props *)
      val full = Name_Space.intern space base
      val {thms, ...} = the (Facts.lookup gctxt facts full)
      val resolved =
        case (thms, idx_opt) of
          ([t], _) => t
        | (_, SOME i) => nth thms (i - 1)
        | (_, NONE) => hd thms
      val _ = assert ("resolved prop matches original for " ^ printed)
                (Thm.eq_thm_prop (th, resolved))
    in
      writeln ("OK  " ^ printed ^ "  ->  base=\"" ^ base ^ "\" idx=" ^
        (case idx_opt of SOME i => string_of_int i | NONE => "NONE"))
    end;
in
  val _ = roundtrip @{thm conjI};
  val _ = map roundtrip @{thms list.distinct};
  val _ = map roundtrip @{thms list.sel};
  val _ = roundtrip @{thm conjunct1};
  val _ = roundtrip @{thm conjunct2};
  val _ = writeln "All print/parse round-trip assertions passed.";
end
\<close>

end
