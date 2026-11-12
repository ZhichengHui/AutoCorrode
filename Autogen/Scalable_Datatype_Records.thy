(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Scalable_Datatype_Records
  imports "HOL-Library.Datatype_Records"
  keywords "scalable_datatype_record" :: thy_defn
begin
(*>*)

section\<open>Datatype records whose declaration scales with the number of fields\<close>

text\<open>\<^verbatim>\<open>scalable_datatype_record\<close> declares a record like \<^verbatim>\<open>datatype_record\<close>
  (\<^theory>\<open>HOL-Library.Datatype_Records\<close>), with the same syntax: a datatype with one constructor
  \<open>make_T\<close> and the fields as selectors, and for each field \<open>f\<close> an update function \<open>update_f\<close>,
  defined like \<^verbatim>\<open>datatype_record\<close>'s and registered as \<^verbatim>\<open>datatype_record_update\<close> (so the record
  lenses of \<^verbatim>\<open>micro_rust_record\<close> are generated alike).

  \<^verbatim>\<open>datatype_record\<close> proves, for every pair of fields \<open>f\<close>, \<open>g\<close>, that updating \<open>f\<close> does not change
  \<open>g\<close> and that the updates of \<open>f\<close> and \<open>g\<close> commute: quadratically many theorems, each proved by
  unfolding the record, so its declaration takes time cubic in the number of fields (a record of
  40 fields takes minutes, one of 80 fields more than an hour). Here only the theorems linear in
  number are proved and declared \<open>[simp]\<close> as \<open>T.record_simps\<close>:
  \<open>f (update_f h r) = h (f r)\<close>, \<open>update_f h (update_f h' r) = update_f (h \<circ> h') r\<close> (as a
  \<open>\<lambda>\<close>-term), \<open>update_f (\<lambda>_. f r) r = r\<close> and \<open>h (f r) = f r \<Longrightarrow> update_f h r = r\<close> (not
  among \<^verbatim>\<open>datatype_record\<close>'s theorems: it proves an update trivial without comparing the
  records field by field). That updating \<open>f\<close> does not change another field
  \<open>g\<close>, \<open>g (update_f h r) = g r\<close>, is proved when needed, by a simproc on \<open>g (\<dots>)\<close>. That updates of
  different fields commute is not a simp rule here. The update syntax \<open>r\<lparr>f := v\<rparr>\<close> of
  \<^verbatim>\<open>datatype_record\<close> is not available for these records.\<close>

ML\<open>
structure Scalable_Datatype_Records =
struct

val dummify = map_types (K dummyT)
fun mk_eq_dummy (lhs, rhs) = Const (\<^const_name>\<open>HOL.eq\<close>, dummyT --> dummyT --> \<^typ>\<open>bool\<close>) $ lhs $ rhs
fun repeat_split_tac ctxt thm = REPEAT_ALL_NEW (CHANGED o Splitter.split_tac ctxt [thm])
fun simp_only_tac simp_thms ctxt =
  REPEAT_ALL_NEW (resolve_tac ctxt @{thms impI allI}) THEN'
    asm_full_simp_tac (put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps simp_thms)

(*unfold the given update definitions, case-split the record and simplify with the selectors*)
fun record_tac split simp_thms defs ctxt =
  Local_Defs.unfold_tac ctxt defs THEN
  PARALLEL_ALLGOALS (repeat_split_tac ctxt split THEN' simp_only_tac simp_thms ctxt)

fun mk_update_defs typ_name lthy =
  let
    val short_name = Long_Name.base_name typ_name
    val {ctrs, casex, selss, split, sel_thmss, injects, ...} = the (Ctr_Sugar.ctr_sugar_of lthy typ_name)
    val ctr = case ctrs of [ctr] => ctr | _ => error "scalable_datatype_record: expected one constructor"
    val sels = case selss of [sels] => sels | _ => error "scalable_datatype_record: expected selectors"
    val sels_dummy = map dummify sels
    val ctr_dummy = dummify ctr
    val casex_dummy = dummify casex
    val len = length sels
    val simp_thms = flat sel_thmss @ injects

    fun mk_name sel = Binding.name ("update_" ^ Long_Name.base_name (dest_Const_name sel))

    (*update_f \<equiv> \<lambda>h r. case r of make x1 .. xn \<Rightarrow> make x1 .. (h xi) .. xn, as datatype_record*)
    fun mk_t idx =
      let
        val body =
          fold_rev (fn pos => fn t => t $ (if len - pos = idx + 1 then Bound len $ Bound pos else Bound pos))
            (0 upto len - 1) ctr_dummy
          |> fold_rev (fn idx => fn t => Abs ("x" ^ Value.print_int idx, dummyT, t)) (1 upto len)
      in Abs ("f", dummyT, casex_dummy $ body) end

    fun define name t =
      Local_Theory.define ((name, NoSyn),
        ((Binding.empty, Code.singleton_default_equation_attrib :: @{attributes [datatype_record_update]}), t))
      #> apfst (apsnd snd)

    val (updates, (lthy'', lthy')) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.map_background_naming (Name_Space.qualified_path false (Binding.name short_name))
      |> @{fold_map 2} define (map mk_name sels) (Syntax.check_terms lthy (map mk_t (0 upto len - 1)))
      ||> `Local_Theory.end_nested

    val phi = Proof_Context.export_morphism lthy' lthy''
    val (update_ts, update_defs) = split_list updates |>> map (Morphism.term phi) ||> map (Morphism.thm phi)

    (*the theorems about one field: their number is linear in the number of fields*)
    fun prove ctxt n =
      let
        val t_dummy = dummify (nth update_ts n)
        val sel_dummy = nth sels_dummy n
        fun prove_prop names mk =
          let
            val (vs, ctxt') = Variable.add_fixes names ctxt
            val frees = map (fn v => Free (v, dummyT)) vs
            val prop = Syntax.check_term ctxt' (HOLogic.mk_Trueprop (mk_eq_dummy (mk frees)))
          in
            Goal.prove_future ctxt' [] [] prop (fn {context, ...} =>
              record_tac split simp_thms [nth update_defs n] context)
            |> singleton (Variable.export ctxt' ctxt)
          end
        val sel_upd_same = prove_prop ["f", "x"] (fn [f, x] => (sel_dummy $ (t_dummy $ f $ x), f $ (sel_dummy $ x)))
        val upd_comp = prove_prop ["f", "g", "x"] (fn [f, g, x] =>
          (t_dummy $ f $ (t_dummy $ g $ x), t_dummy $ Abs ("a", dummyT, f $ (g $ Bound 0)) $ x))
        val upd_sel = prove_prop ["x"] (fn [x] => (t_dummy $ Abs ("_", dummyT, sel_dummy $ x) $ x, x))
        (*update_f h r = r if h does not change f r: without it, simp proves such an equation of
          records field by field (expand), one simproc proof per field*)
        val upd_triv =
          let
            val ([h, x], ctxt') = Variable.add_fixes ["h", "x"] ctxt
            val (h, x) = (Free (h, dummyT), Free (x, dummyT))
            val prop = Syntax.check_term ctxt' (Logic.mk_implies
              (HOLogic.mk_Trueprop (mk_eq_dummy (h $ (sel_dummy $ x), sel_dummy $ x)),
               HOLogic.mk_Trueprop (mk_eq_dummy (t_dummy $ h $ x, x))))
          in
            Goal.prove_future ctxt' [] [] prop (fn {context, ...} =>
              record_tac split simp_thms [nth update_defs n] context)
            |> singleton (Variable.export ctxt' ctxt)
          end
      in [sel_upd_same, upd_comp, upd_sel, upd_triv] end

    val thms = flat (map (prove lthy'') (0 upto len - 1))

    (*on g (update_f h r) with f \<noteq> g: the equation g (update_f h r) = g r, proved for h and r fixed
      and instantiated to the term*)
    val update_names = map dest_Const_name update_ts
    (*the theorems for the proof at an instance of the record's type parameters*)
    val varifyT = map (Drule.zero_var_indexes o Thm.varifyT_global)
    val (split_v, simp_thms_v, update_defs_v) = (hd (varifyT [split]), varifyT simp_thms, varifyT update_defs)
    fun proc _ ctxt ct =
      (case Thm.term_of ct of
        sel $ (upd $ h $ r) =>
          (case (find_index (fn s => s = dest_Const_name sel) (map dest_Const_name sels),
                 find_index (fn u => (case upd of Const (c, _) => c = u | _ => false)) update_names) of
            (j, i) =>
              if j < 0 orelse i < 0 orelse i = j then NONE
              else
                let
                  val ([hn, rn], ctxt') = Variable.variant_fixes ["h", "r"] ctxt
                  val (hv, rv) = (Free (hn, fastype_of h), Free (rn, fastype_of r))
                  (*the update may change type parameters that occur in no field: the selector
                    of the updated record is at another instance than the one of r*)
                  val sel_r = Const (dest_Const_name sel, fastype_of r --> range_type (fastype_of sel))
                  val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (sel $ (upd $ hv $ rv), sel_r $ rv))
                  val thm =
                    Goal.prove ctxt' [] [] prop (fn {context, ...} =>
                      record_tac split_v simp_thms_v [nth update_defs_v i] context)
                    |> singleton (Variable.export ctxt' ctxt)
                    |> Drule.zero_var_indexes
                    |> mk_meta_eq
                in
                  SOME (Thm.instantiate (Thm.first_order_match (Thm.lhs_of thm, ct)) thm)
                end)
      | _ => NONE)
      handle Pattern.MATCH => NONE | ERROR _ => NONE

    (*the simproc applies at every instance of the record's type parameters (schematic in the
      selectors): they become type variables new to the context, which define_simproc generalises*)
    val lhss =
      map (fn sel => sel $ Var (("r", 0), domain_type (fastype_of sel))) sels
      |> (fn ts => fst (Variable.importT_terms ts lthy''))
  in
    lthy''
    |> Local_Theory.map_background_naming (Name_Space.mandatory_path short_name)
    |> Local_Theory.note ((Binding.name "record_simps", @{attributes [simp]}), thms)
    |> snd
    |> Simplifier.define_simproc
         {passive = false, name = Binding.name "sel_update", kind = Simplifier.Simproc,
          lhss = lhss, proc = proc, identifier = []}
    |> snd
    |> Local_Theory.restore_background_naming lthy
  end

fun record binding opts tyargs args lthy =
  let
    val constructor = (((Binding.empty, Binding.map_name (fn c => "make_" ^ c) binding), args), NoSyn)
    val datatyp = ((tyargs, binding), NoSyn)
    val dtspec = ((opts, false), [(((datatyp, [constructor]), (Binding.empty, Binding.empty, Binding.empty)), [])])
  in
    BNF_FP_Def_Sugar.co_datatypes BNF_Util.Least_FP BNF_LFP.construct_lfp dtspec lthy
    |> mk_update_defs (Local_Theory.full_name lthy binding)
  end

fun record_cmd binding opts tyargs args lthy =
  record binding (opts lthy)
    (map (apsnd (apfst (Syntax.parse_typ lthy) o apsnd (Typedecl.read_constraint lthy))) tyargs)
    (map (apsnd (Syntax.parse_typ lthy)) args) lthy

val parse_ctr_options =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.list1 (Plugin_Name.parse_filter >> K) --| \<^keyword>\<open>)\<close> >>
    (fn fs => fold I fs (K Plugin_Name.default_filter))) (K Plugin_Name.default_filter)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>scalable_datatype_record\<close>
    "a record based on the datatype package, without the theorems quadratic in the number of fields"
    ((parse_ctr_options -- BNF_Util.parse_type_args_named_constrained -- Parse.binding) --
      (\<^keyword>\<open>=\<close> |-- Scan.repeat1 (Parse.binding -- (\<^keyword>\<open>::\<close> |-- Parse.!!! Parse.typ)))
     >> (fn (((opts, tyargs), binding), args) => record_cmd binding opts tyargs args))

end
\<close>

(*<*)
end
(*>*)
