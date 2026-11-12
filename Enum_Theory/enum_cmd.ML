(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Enum command: typedef-based construction with all theorems proven *)

signature ENUM_CMD =
sig
  val enum_trace_config: bool Config.T
  val enum_sync_prove_config: bool Config.T
  val enum_eq_simproc: simproc
  val enum_cmd: (binding * (binding * string list) list) -> local_theory -> local_theory
end

structure Enum_Cmd : ENUM_CMD =
struct

open Ctr_Sugar_Util

val enum_trace_config = Attrib.setup_config_bool (Binding.name "enum_trace") (fn _ => false)
val enum_sync_prove_config = Attrib.setup_config_bool (Binding.name "enum_sync_prove") (fn _ => true)


fun timer ctx timer msg = (if Config.get ctx enum_trace_config
  then tracing (msg ^ ": " ^ Timing.message (Timing.result timer))
  else (); Timing.start ())

fun time_tactic msg ctx tac =
  if Config.get ctx enum_trace_config then
    fn th =>
      let
        val start = Timing.start ()
        val res = tac th |> Seq.list_of |> Seq.of_list
        val tim = Timing.result start
        val _ = tracing (msg ^ ": " ^ Timing.message tim)
      in
        res
      end
  else tac

fun trace_prove ctxt xs asms prop tac = 
  if Config.get ctxt enum_sync_prove_config then
    Goal.prove ctxt xs asms prop tac
  else
    Goal.prove_sorry ctxt xs asms prop tac

fun par_do_the_works works =
    works
  |> chop_groups 10
  |> Par_List.map (map (fn f => f ()))
  |> List.concat

fun do_the_works ctxt works =
  if Config.get ctxt enum_sync_prove_config then
    (* if we do synchronous proving, at least we can use parallelism to speed up the proofs *)
    par_do_the_works works
  else
    (* if we do asynchronous proving, then we just don't bother doing optimization *)
    map (fn f => f ()) works

(* The sum type of a list of types, as a balanced tree: the first half on the left, the rest on
   the right. A value of the nth type is then O(log n) injections deep, so the case combinator
   and the proofs about one constructor stay small for enums with many constructors. *)
fun halves tys = chop (length tys div 2) tys

(* The sum type of the types tys (one or more), and for each of them the injection of its values
   into the sum type, built in one pass over the tree *)
fun sum_tree [ty] = (ty, [I])
  | sum_tree tys =
    let
      val (l, r) = halves tys
      val ((a, injs_l), (b, injs_r)) = (sum_tree l, sum_tree r)
    in
      (@{Type \<open>sum a b\<close>},
       map (fn inj => fn t => @{Const\<open>Inl a b for \<open>inj t\<close>\<close>}) injs_l @
       map (fn inj => fn t => @{Const\<open>Inr b a for \<open>inj t\<close>\<close>}) injs_r)
    end

fun get_type_thm_local ctxt typ thm_suffix =
  let
    fun type_name_of (Type (name, _)) = Long_Name.base_name name
      | type_name_of _ = ""

    val typ_name = type_name_of typ
  in
    if typ_name = "" then raise ERROR "thm is not found!"
    else
      let
        val thm_name = typ_name ^ "." ^ thm_suffix
      in
        Proof_Context.get_thm ctxt thm_name
      end
  end


fun has_type_thm_local ctxt typ thm_suffix =
  (get_type_thm_local ctxt typ thm_suffix; true)
  handle ERROR _ => false

fun has_is_enum_thm ctxt typ = has_type_thm_local ctxt typ "is_enum"

fun get_ctor_def ctxt typ ctor =
  let
    val name = dest_Const_name ctor
    val basename = Long_Name.base_name name
  in
    get_type_thm_local ctxt typ (basename ^ "_def")
  end

fun same_ctor af bf =
  let
    val aname = dest_Const_name af
    val bname = dest_Const_name bf
  in
    aname = bname
  end

fun only_simpset context thms =
  context |> Simplifier.clear_simpset |> Simplifier.add_simps thms

fun enum_eq_proc ctxt ct =
  let
    val orig_t = Thm.term_of ct
  in
    case orig_t of
      @{Const_\<open>HOL.eq T for a b\<close>} => if has_is_enum_thm ctxt T
      then
        let
          val (af, _) = strip_comb a
          val (bf, _) = strip_comb b
        in
          (if not (same_ctor af bf) then
            let
              val Abs_inject = get_type_thm_local ctxt T "Abs_inject"
              val adef = get_ctor_def ctxt T af
              val bdef = get_ctor_def ctxt T bf
              val goal = orig_t |> HOLogic.mk_not |> HOLogic.mk_Trueprop
              val thm = trace_prove ctxt [] [] goal (fn {context, ...} =>
                simp_tac (only_simpset context ([Abs_inject, adef, bdef] @ @{thms sum.distinct sum.inject simp_thms UNIV_I lessThan_iff triv_forall_equality})) 1)
            in
              SOME (thm RS @{thm Eq_FalseI})
            end
          else NONE)
          handle ERROR _ => NONE |  TERM _ => NONE
        end
      else NONE
    | _ => NONE
  end

val enum_eq_simproc = @{simproc_setup\<open>enum_eq (\<open>x = y\<close>) = \<open>K enum_eq_proc\<close>\<close>}

fun add_and_prove_is_enum typ_name lthy =
  let
    val is_enum_prop = HOLogic.mk_Trueprop @{term True}
    val is_enum_thm = trace_prove lthy [] [] is_enum_prop
      (fn {context, ...} => rtac context @{thm TrueI} 1)

    val is_simpl_binding = Binding.qualify true typ_name (Binding.name "is_enum")
    val (_, lthy') = lthy
      |> Local_Theory.note ((is_simpl_binding, []), [is_enum_thm]) 
  in
    lthy'
  end

fun mk_case_certificate ctxt raw_thms =
  let
    val thms as thm1 :: _ = raw_thms
      |> Conjunction.intr_balanced
      |> Thm.unvarify_global (Proof_Context.theory_of ctxt)
      |> Conjunction.elim_balanced (length raw_thms)
      |> map Simpdata.mk_meta_eq
      |> map Drule.zero_var_indexes
    val params = Term.add_free_names (Thm.prop_of thm1) []
    val rhs = thm1
      |> Thm.prop_of |> Logic.dest_equals |> fst |> Term.strip_comb
      ||> fst o split_last |> list_comb
    val lhs = Free (singleton (Name.variant_list params) "case", Term.fastype_of rhs)
    val assum = Thm.cterm_of ctxt (Logic.mk_equals (lhs, rhs))
  in
    thms
    |> Conjunction.intr_balanced
    |> rewrite_rule ctxt [Thm.symmetric (Thm.assume assum)]
    |> Thm.implies_intr assum
    |> Thm.generalize (Names.empty, Names.make_set params) 0
    |> Axclass.unoverload ctxt
    |> Thm.varifyT_global
  end

(* The code equations for HOL.equal of the simple representation (constructors without arguments):
   one per pair of constructors, and the reflexivity equation for nbe *)
fun mk_equal_eqns typ constr_terms thy =
  let
    val equal_const = Const (@{const_name HOL.equal}, typ --> typ --> HOLogic.boolT)
    fun mk_goal (ci, cj) =
      HOLogic.mk_Trueprop (HOLogic.mk_eq (equal_const $ ci $ cj, if ci aconv cj then @{term True} else @{term False}))
    val eqns = map (fn pair =>
      Goal.prove_sorry_global thy [] [] (mk_goal pair) (fn {context, ...} =>
        simp_tac (Simplifier.add_simps @{thms equal_eq} context) 1)
      |> Simpdata.mk_eq) (map_product pair constr_terms constr_terms)
  in
    (hd eqns, eqns)
  end

(* The code equations for HOL.equal of the complex representation: x = y iff their
   representations are equal, with one code equation for Rep per constructor (rep_eqns), instead
   of one equation per pair of constructors (mk_equal_eqns) *)
fun equal_eqns_by_rep typ rep_const Rep_inject rep_eqns thy =
  let
    val (x, y) = (Free ("x", typ), Free ("y", typ))
    val equal = Const (@{const_name HOL.equal}, typ --> typ --> HOLogic.boolT)
    fun prove xs prop = Goal.prove_global thy xs [] (HOLogic.mk_Trueprop prop)
      (fn {context, ...} => simp_tac (put_simpset HOL_basic_ss context
        |> Simplifier.add_simps (Rep_inject :: @{thms equal_eq simp_thms})) 1)
      |> Simpdata.mk_eq
    val by_rep = prove ["x", "y"] (HOLogic.mk_eq (equal $ x $ y, HOLogic.mk_eq (rep_const $ x, rep_const $ y)))
    val refl = prove ["x"] (HOLogic.mk_eq (equal $ x $ x, @{term True}))
  in
    (refl, false) :: (by_rep, true) :: map (rpair true o Thm.varifyT_global) rep_eqns
  end

(* equal_eqns: the code equations of HOL.equal, with their nbe flags *)
fun add_equal_instance typ constr_terms case_eq_thms equal_eqns thy =
  let
    val tyco = dest_Type_name typ
    fun add_eq_def lthy_inst =
      let
        fun mk_side const_name =
          Const (const_name, typ --> typ --> HOLogic.boolT) $ Free ("x", typ) $ Free ("y", typ)
        val spec =
          HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_side @{const_name HOL.equal}, mk_side @{const_name HOL.eq}))
          |> Syntax.check_term lthy_inst
        val ((_, (_, raw_def)), lthy_inst') =
          Specification.definition {verbose = false} NONE [] [] (Binding.empty_atts, spec) lthy_inst
        val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy_inst')
        val def = singleton (Proof_Context.export lthy_inst' thy_ctxt) raw_def
      in
        (def, lthy_inst')
      end
    fun eq_tac ctxt thms =
      Class.intro_classes_tac ctxt [] THEN ALLGOALS (Proof_Context.fact_tac ctxt thms)
  in
    thy
    |> Class.instantiation ([tyco], [], @{sort equal})
    |> add_eq_def
    |-> Class.prove_instantiation_exit_result (map o Morphism.thm) eq_tac o single
    |> snd
    |> Code.declare_datatype_global
         (map (fn c => (dest_Const_name c, fastype_of c)) constr_terms)
    |> (fn thy' =>
         let
           val ctxt = Proof_Context.init_global thy'
           val case_thms = map Thm.varifyT_global case_eq_thms
         in thy'
           |> Code.declare_default_eqns_global (equal_eqns thy')
           |> Code.declare_default_eqns_global (map (rpair true) (rev case_thms))
           |> Code.declare_case_global (mk_case_certificate ctxt case_thms)
         end)
  end

(* The induction rule: P holds for Abs y for every y. The quantifier over y is split along the
   sum type (split_sum_all) and the tuples (split_paired_All, unit_all) down to the injections of
   the constructors' arguments, where the premises (constructor definitions unfolded) apply. The
   body is simplified before its quantifier is split, so a constructor argument that is itself
   a sum or a tuple is not split further. *)
fun prove_complex_induct lthy2 vars ind_prop Abs_induct constr_defs =
  trace_prove lthy2 vars [] ind_prop
    (fn {context, ...} =>
      rewrite_goal_tac context constr_defs 1 THEN
      Subgoal.FOCUS (fn {context = ctxt, prems, ...} =>
        resolve_tac ctxt [Abs_induct] 1 THEN
        Object_Logic.full_atomize_tac ctxt 1 THEN
        simp_tac (put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps
          (prems @ @{thms UNIV_I simp_thms split_sum_all split_paired_All} @
           [@{lemma \<open>(\<forall>x::unit. P x) \<longleftrightarrow> P ()\<close> by (metis old.unit.exhaust)}])) 1) context 1)

(* prove exhaust using induction principle *)
fun solve_exhaust_tac context x_ind goal induct_thm = 
  let
    val x = Thm.cterm_of context x_ind
    val g = lambda x_ind (Induct.atomize_term context goal)
    val induct = infer_instantiate' context [SOME (Thm.cterm_of context g), SOME x] induct_thm
  in
    EVERY [
      Induct.atomize_tac context 1,
      rtac context induct 1,
      ALLGOALS (Induct.rulify_tac context),
      ALLGOALS (fn i => Subgoal.FOCUS (fn {context, prems, ...} =>
        resolve_tac context [nth prems (i - 1)] 1 THEN
        simp_tac (context |> Simplifier.clear_simpset) 1) context i)
    ]
  end

(* The exhaustion rule [| \<And>xs. x = C1 xs \<Longrightarrow> P; ... |] \<Longrightarrow> P, forward from the induction rule
   instantiated with \<lambda>y. x = y \<longrightarrow> P: each of its premises is discharged by a small proof from the
   corresponding premise of the goal, so the proof state never holds all constructors' cases *)
fun forward_exhaust_tac context x_ind induct_thm =
  Subgoal.FOCUS (fn {context = ctxt, prems, concl, ...} =>
    let
      val P = HOLogic.dest_Trueprop (Thm.term_of concl)
      val T = fastype_of x_ind
      val Q = Abs ("y", T, HOLogic.mk_imp (HOLogic.mk_eq (x_ind, Bound 0), P))
      val inst = map (fn (v as (_, vT)) => (v, Thm.cterm_of ctxt (if vT = T then x_ind else Q)))
        (Term.add_vars (Thm.prop_of induct_thm) [])
      val induct_inst = Thm.instantiate (TVars.empty, Vars.make inst) induct_thm
        |> Conv.fconv_rule (Thm.beta_conversion true)
      fun discharge prem acc =
        Thm.implies_elim acc (Goal.prove_internal ctxt [] (Thm.cprem_of acc 1) (fn _ =>
          resolve_tac ctxt @{thms impI} 1 THEN resolve_tac ctxt [prem] 1 THEN assume_tac ctxt 1))
      val final = @{thm mp} OF [fold discharge prems induct_inst, @{thm refl}]
    in resolve_tac ctxt [final] 1 end) context 1

fun add_and_prove_exhaust lthy typ_name vars goal tac constr_names =
  let
    val exhaust_thm = trace_prove lthy vars [] goal (fn {context, ...} => tac context)
    val exhaust_binding = Binding.qualify true typ_name (Binding.name "exhaust")
    val case_names_att = Attrib.internal \<^here> (fn _ => Rule_Cases.case_names constr_names)
  in
    (exhaust_thm, lthy |> Local_Theory.note ((exhaust_binding, case_names_att :: @{attributes [cases type]}), [exhaust_thm]) |> snd)
  end

fun solve_split_tac context x_varc case_eq_thms exhaust_thm =
  let
    fun solve_tac context i =
      Object_Logic.rulify_tac context i THEN
            asm_full_simp_tac (only_simpset context case_eq_thms) i
  in
    EVERY [
      rtac context @{thm HOL.iffI} 1,
      REPEAT (rtac context @{thm conjI} 1 THEN
        solve_tac context 1) |> time_tactic "split repeat" context,
      solve_tac context 1,

      REPEAT (etac context @{thm conjE} 1),
      Object_Logic.rulify_tac context 1,
      rtac context (Thm.instantiate' [] [SOME x_varc] exhaust_thm) 1,
      ALLGOALS (fn i => Subgoal.FOCUS
        (fn {context, prems, ...} =>
          let
            val eq = List.last prems
            val i' = i - 1
            val case_eq = nth case_eq_thms i'
          in
            asm_full_simp_tac (only_simpset context [eq, case_eq]) 1 THEN
            rtac context (nth prems i') 1 THEN
            rtac context eq 1
          end)
        context i) |> time_tactic "split to simp" context
    ]
  end

(* The split rule P (case x of ..) = ((\<forall>xs. x = C1 xs \<longrightarrow> P (f1 xs)) \<and> ...), each direction
   built from one small proof per constructor (arg_counts: the numbers of their arguments) *)
fun forward_split_tac context x_ind case_eq_thms exhaust_thm arg_counts =
  let
    val n = length arg_counts
    val case_eqs = map mk_meta_eq case_eq_thms
    fun conjuncts 1 th = [th]
      | conjuncts k th = (th RS @{thm conjunct1}) :: conjuncts (k - 1) (th RS @{thm conjunct2})
    fun dest_conjs 1 t = [t]
      | dest_conjs k (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ a $ b) = a :: dest_conjs (k - 1) b
      | dest_conjs _ t = raise TERM ("forward_split_tac: not a conjunction", [t])
    (* P (case x) \<Longrightarrow> each clause: rewrite x to the constructor, then the case *)
    val to_clauses = Subgoal.FOCUS (fn {context = ctxt, prems, concl, ...} =>
      let
        val H = hd prems
        fun clause (j, cl) = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop cl) (fn {context = c, ...} =>
          REPEAT (resolve_tac c @{thms allI} 1) THEN resolve_tac c @{thms impI} 1 THEN
          Subgoal.FOCUS (fn {context = c', prems = eqs, ...} =>
            resolve_tac c' [rewrite_rule c' [mk_meta_eq (hd eqs), nth case_eqs j] H] 1) c 1)
        val clauses = dest_conjs n (HOLogic.dest_Trueprop (Thm.term_of concl))
      in resolve_tac ctxt [foldr1 (fn (a, b) => @{thm conjI} OF [a, b]) (map_index clause clauses)] 1 end)
    (* the clauses \<Longrightarrow> P (case x): by exhaustion, with the clause of the constructor *)
    val from_clauses = Subgoal.FOCUS (fn {context = ctxt, prems, concl, ...} =>
      let
        val cls = conjuncts n (hd prems)
        val goal = HOLogic.dest_Trueprop (Thm.term_of concl)
        val inst = map (fn (v as (_, vT)) => (v, Thm.cterm_of ctxt (if vT = fastype_of x_ind then x_ind else goal)))
          (Term.add_vars (Thm.prop_of exhaust_thm) [])
        val exhaust_inst = Thm.instantiate (TVars.empty, Vars.make inst) exhaust_thm
        fun discharge ((i, cl), k) acc =
          Thm.implies_elim acc (Goal.prove_internal ctxt [] (Thm.cprem_of acc 1) (fn _ =>
            Subgoal.FOCUS (fn {context = c', prems = eqs, ...} =>
              rewrite_goal_tac c' [mk_meta_eq (hd eqs), nth case_eqs i] 1 THEN
              resolve_tac c' [@{thm mp} OF [funpow k (fn th => th RS @{thm spec}) cl, hd eqs]] 1) ctxt 1))
      in resolve_tac ctxt [fold discharge (map_index I cls ~~ arg_counts) exhaust_inst] 1 end)
  in
    resolve_tac context @{thms iffI} 1 THEN to_clauses context 1 THEN from_clauses context 1
  end

fun solve_split_asm_tac context split_thm =
  simp_tac (only_simpset context (split_thm :: @{thms de_Morgan_disj de_Morgan_conj disj_not1 not_ex simp_thms})) 1 |> time_tactic "split asm" context

fun enum_cmd_complex (typ_binding, constrs) lthy =
  let
    val _ = if null constrs then error "Empty enum not allowed" else ()
    val time = timer lthy
    val timer = time (Timing.start ())
    val typ_name = Binding.name_of typ_binding

    (* Parse constructor argument types *)
    val constrs_with_typs : (binding * typ list) list =
      map (fn (c, typ_strs) => (c, Syntax.read_typs lthy typ_strs)) constrs

    (* Build representation type as sum of products *)
    val prod_typs = map (HOLogic.mk_tupleT o snd) constrs_with_typs
    val (rep_typ, injections) = sum_tree prod_typs
    val timer = time (timer "Setup")

    (* Step 1: Define the type using typedef *)
    val typedef_set = HOLogic.mk_UNIV rep_typ

    (* Create qualified bindings for Abs, Rep, and type_definition *)
    val typedef_bindings = SOME {
      Abs_name = Binding.qualify true typ_name (Binding.name "Abs"),
      Rep_name = Binding.qualify true typ_name (Binding.name "Rep"),
      type_definition_name = Binding.qualify true typ_name (Binding.name "type_definition")
    }

    val ((_, (typ_info, typedef_info)), lthy1) = lthy
      |> Typedef.add_typedef {overloaded = false}
           (typ_binding, [], NoSyn) typedef_set typedef_bindings
           (fn ctxt => resolve_tac ctxt @{thms UNIV_witness} 1)
      ||> add_and_prove_is_enum typ_name

    val { abs_type = typ, Abs_name, Rep_name, ...} = typ_info
    val abs_const = Const (Abs_name, rep_typ --> typ)
    val rep_const = Const (Rep_name, typ --> rep_typ)

    (* Get typedef theorems *)
    val { Abs_induct,
          Abs_inverse,
          Abs_inject,
          Rep_inject,
           ...} = typedef_info
    val timer = time (timer "Typedef")

    (* Step 2: Define constructors *)
    fun define_constructor (idx, (c_binding, arg_typs)) lthy =
      let
        (* Build constructor body: \<lambda>x1 ... xn. Abs (Inl/Inr (x1, ..., xn)) *)
        val (var_terms, lthy1) = mk_Frees "x" arg_typs lthy
        val tuple = HOLogic.mk_tuple var_terms
        val injected = nth injections idx tuple
        val abs_applied = abs_const $ injected
        (* Use absfree to properly abstract over Free variables *)
        val constr_tm = fold_rev lambda var_terms abs_applied

        (* Qualify constructor name *)
        val qual_c_binding = Binding.qualify false typ_name c_binding
        val def_binding = Binding.qualify true typ_name (Binding.suffix_name "_def" c_binding)

        val (_, lthy') = lthy1
          |> Local_Theory.define ((qual_c_binding, NoSyn),
                                  ((def_binding, []), constr_tm))
      in
        (qual_c_binding, lthy')
      end

    val (constr_qbindings, lthy2) = lthy1
      |> snd o Local_Theory.begin_nested
      |> fold_map define_constructor (map_index I constrs_with_typs)
      ||> Local_Theory.end_nested
    val constr_terms = map (fn (c, args) =>
      Const (Local_Theory.full_name lthy2 c, args ---> typ))
      (constr_qbindings ~~ map snd constrs_with_typs)
    val constr_defs = map (get_type_thm_local lthy2 typ o Binding.name_of o Binding.suffix_name "_def") constr_qbindings
    val timer = time (timer "Constructor Definitions")

    (* Step 3: Prove induction principle *)
    (* \<lbrakk> ?P C1; ?P C2; ... \<rbrakk> \<Longrightarrow> ?P ?x *)
    val ((P_ind, x_ind), _) =
      lthy2
      |> mk_Frees "P" [typ --> HOLogic.boolT]
      ||>> mk_Frees "x" [typ]
      |>> map_prod the_single the_single

    fun mk_ind_prem c_const arg_typs =
      let
        val vars = map_index (fn (i, ty) => Var (("x" ^ Int.toString (i + 1), 0), ty)) arg_typs
        val c_applied = list_comb (c_const, vars)
        val body = P_ind $ c_applied
        val body_prop = HOLogic.mk_Trueprop body
      in
        fold_rev Logic.all vars body_prop
      end

    val ind_prems_prop = map2 mk_ind_prem constr_terms (map snd constrs_with_typs)
    val ind_concl = P_ind $ x_ind
    val ind_prop = Logic.list_implies (ind_prems_prop, HOLogic.mk_Trueprop ind_concl)

    val vars = Variable.add_free_names lthy2 ind_prop []
    val induct_thm = prove_complex_induct lthy2 vars ind_prop Abs_induct constr_defs

    (* Add the induction theorem to the context with qualified name and induct_type attribute *)
    val induct_binding = Binding.qualify true typ_name (Binding.name "induct")
    val constr_names = map (Binding.name_of o fst) constrs_with_typs
    val case_names_att = Attrib.internal \<^here> (fn _ => Rule_Cases.case_names constr_names)
    val (_, lthy3) = lthy2
      |> Local_Theory.note ((induct_binding, case_names_att :: @{attributes [induct type]}), [induct_thm])
    val timer = time (timer "Induction Principle")

    (* Step 4: Define case combinator *)
    (* case_<typ> : (arg_typs1 -> 'a) -> ... -> (arg_typsN -> 'a) -> <typ> -> 'a *)
    val (Ta, lthy4) = map_prod the_single I (mk_TFrees 1 lthy3)

    (* Create function types for each case *)
    fun mk_case_arg_type arg_typs = arg_typs ---> Ta

    val case_arg_typs = map (mk_case_arg_type o snd) constrs_with_typs
    val case_typ = case_arg_typs ---> typ --> Ta

    (* Create case function variables *)
    val (case_funs, lthy5) = mk_Frees "f" case_arg_typs lthy4

    (* Build case body: match on constructor and apply corresponding function *)
    (* For each constructor C x1 ... xn, we want: if input = C x1 ... xn then f x1 ... xn *)
    fun mk_case_branch arg_typs f =
      let
        val (args, _) = mk_Frees "x" arg_typs lthy5
      in
        HOLogic.tupled_lambda (HOLogic.mk_tuple args) (list_comb (f, args))
      end

    val branches = map2 mk_case_branch (map snd constrs_with_typs) case_funs

    (* Use Abs_induct and constructor definitions to build the case function *)
    (* case f1 f2 ... x = case (Rep x) of Inl a => f1 a | Inr (Inl b) => f2 b | ... *)
    val case_body_var = rep_const $ x_ind

    (* the branches split in halves as the types in sum_tree *)
    fun mk_case_of_sum [] _ _ = raise ERROR "mk_case_of_sum: empty list"
      | mk_case_of_sum [rhs] var _ = rhs $ var
      | mk_case_of_sum rhss sum_var ctx =
        let
          val (l, r) = halves rhss
          val @{Type \<open>sum a b\<close>} = fastype_of sum_var
          val ([left_var, right_var], ctx') = mk_Frees "b" [a, b] ctx
          val left_branch = lambda left_var (mk_case_of_sum l left_var ctx')
          val right_branch = lambda right_var (mk_case_of_sum r right_var ctx')
        in
          @{Const \<open>case_sum a Ta b for left_branch right_branch sum_var\<close>}
        end

    val case_body = mk_case_of_sum branches case_body_var lthy5
    val case_tm = fold_rev lambda case_funs (lambda x_ind case_body)

    (* Define the case combinator *)
    val case_binding = Binding.qualify true typ_name (Binding.name "case")
    val case_def_binding = Binding.qualify true typ_name (Binding.name "case_def")

    val ((case_const, (_, case_def)), lthy6) = lthy5
      |> Local_Theory.define ((case_binding, NoSyn),
                              ((case_def_binding, []), case_tm))
    val phi = Local_Theory.target_morphism lthy6
    val case_const = Morphism.term phi case_const
    val case_const = Const (dest_Const_name case_const, case_typ)
    val case_def = Morphism.thm phi case_def

    (* Register with Case_Translation for pattern matching *)
    val lthy7 = lthy6
      |> Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
           (fn _ => Case_Translation.register case_const constr_terms)
    val timer = time (timer "Case expression")

    (* case f1 .. fn x \<equiv> the case tree on Rep x, for all f1 .. fn and x: unfolding the case
       combinator (a \<lambda>-term of n + 1 arguments) costs time quadratic in n, so it is done once *)
    val case_app =
      let
        val lhs = list_comb (case_const, case_funs @ [x_ind])
        val rhs = case_body
        val vars = map (fst o dest_Free) (case_funs @ [x_ind])
      in
        Goal.prove lthy7 [] [] (Logic.mk_equals (lhs, rhs)) (fn {context, ...} =>
          rewrite_goal_tac context [case_def] 1 THEN resolve_tac context @{thms Pure.reflexive} 1)
        |> Thm.generalize (Names.empty, Names.make_set vars) 0
      end

    (* Rep (Ci x1 .. xk) = injection of (x1, .., xk), the code equations of Rep
       and the first step of the case equations *)
    fun mk_rep_eqn (idx, (c_term, arg_typs)) =
      let
        val (xs, _) = mk_Frees "x" arg_typs lthy7
        val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (rep_const $ list_comb (c_term, xs), nth injections idx (HOLogic.mk_tuple xs)))
      in
        trace_prove lthy7 (map (fst o dest_Free) xs) [] prop (fn {context, ...} =>
          Local_Defs.unfold_tac context [nth constr_defs idx] THEN
          simp_tac (put_simpset HOL_basic_ss context |> Simplifier.add_simps [Abs_inverse, @{thm UNIV_I}]) 1)
      end
    val rep_eqns = map_index mk_rep_eqn (constr_terms ~~ map snd constrs_with_typs)

    (* Step 5: Prove case equality theorems *)
    (* For each constructor Ci: case f1 ... fn (Ci x1 ... xk) = fi x1 ... xk, forward from case_app
       at x = Ci x1 .. xk: Rep (Ci x1 .. xk) is the injection, which selects the branch of the case
       tree (a goal of this size for each constructor would take time quadratic in n to prove) *)
    val x_var = (fst (dest_Free x_ind), 0)
    val case_ss = put_simpset HOL_basic_ss lthy7
      |> Simplifier.add_simps @{thms sum.case prod.case}
      |> Simplifier.add_cong @{thm sum.case_cong_weak}
    fun mk_case_eq_thm (idx, (c_term, arg_typs)) =
      let
        val (xs, _) = mk_Frees "x" arg_typs lthy7
        val th = infer_instantiate lthy7 [(x_var, Thm.cterm_of lthy7 (list_comb (c_term, xs)))] case_app
          |> Conv.fconv_rule (Conv.arg_conv (Simplifier.rewrite (case_ss |> Simplifier.add_simps [nth rep_eqns idx])))
        val expected = list_comb (Var ((fst (dest_Free (nth case_funs idx)), 0), nth case_arg_typs idx), xs)
        val _ = if snd (Logic.dest_equals (Thm.prop_of th)) aconv expected then ()
          else raise THM ("enum: case equation of constructor " ^ string_of_int idx, 0, [th])
        val eq = th RS @{thm meta_eq_to_obj_eq}
        val eq = Thm.generalize (Names.empty, Names.make_set (map (fst o dest_Free) xs)) (Thm.maxidx_of eq + 1) eq
        (* stated as before (the form the code generator's case certificate expects) and proved
           by the derived equation *)
        val case_fun_vars = mk_Frees "f" case_arg_typs lthy7 |> fst
        val goal = fold_rev Logic.all (xs @ case_fun_vars) (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (list_comb (case_const, case_fun_vars @ [list_comb (c_term, xs)]), list_comb (nth case_fun_vars idx, xs))))
      in
        trace_prove lthy7 [] [] goal (fn {context, ...} => resolve_tac context [eq] 1)
      end

    val case_eq_thms = map_index mk_case_eq_thm (constr_terms ~~ map snd constrs_with_typs)

    (* Ci x1 .. xk = Ci y1 .. yk \<longleftrightarrow> x1 = y1 \<and> .. \<and> xk = yk, as for a datatype *)
    fun mk_inject (idx, (c_term, arg_typs)) =
      let
        val (xs, ctxt') = mk_Frees "x" arg_typs lthy7
        val (ys, _) = mk_Frees "y" arg_typs ctxt'
        val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (HOLogic.mk_eq (list_comb (c_term, xs), list_comb (c_term, ys)),
          foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) xs ys)))
      in
        trace_prove lthy7 (map (fst o dest_Free) (xs @ ys)) [] prop (fn {context, ...} =>
          Local_Defs.unfold_tac context [nth constr_defs idx] THEN
          simp_tac (put_simpset HOL_basic_ss context
            |> Simplifier.add_simps (Abs_inject :: @{thms UNIV_I sum.inject prod.inject simp_thms})) 1)
      end
    val inject_thms = map_index I (constr_terms ~~ map snd constrs_with_typs)
      |> filter_out (null o snd o snd) |> map mk_inject

    (* Store case theorems as ENUM.cases with simp attribute *)
    val cases_binding = Binding.qualify true typ_name (Binding.name "cases")
    val ((_, _), lthy8) = lthy7
      |> Local_Theory.note ((Binding.qualify true typ_name (Binding.name "inject"), @{attributes [simp]}), inject_thms)
      |> snd
      |> Local_Theory.note ((cases_binding, @{attributes [simp]}), case_eq_thms)
    val timer = time (timer "Case Equalities")

    (* Step 6: Prove exhaustiveness theorem *)
    val P = lthy8 |> Variable.variant_fixes ["P"] |> fst |> the_single |> (fn P => Free (P, HOLogic.boolT)) |> HOLogic.mk_Trueprop

    fun exhaust_case ctor argTs =
      let
        val vars = mk_Frees "x" argTs lthy8 |> fst
        val apped = list_comb (ctor, vars)
        val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (x_ind, apped))
      in
        fold_rev Logic.all vars (Logic.mk_implies (eq, P))
      end

    val premises = map2 exhaust_case constr_terms (map snd constrs_with_typs)
    val goal = Logic.list_implies (premises, P)
    val vars = Variable.add_free_names lthy8 goal []
    val constr_names = map (Binding.name_of o fst) constrs_with_typs
    val (exhaust_thm, lthy9) =
      add_and_prove_exhaust lthy8 typ_name vars goal (fn ctxt => forward_exhaust_tac ctxt x_ind induct_thm) constr_names
    val _ = time (timer "Case Split")

    (* Step 7: Prove split theorems *)
    (* The split theorem allows case expressions to be split into individual cases *)
    (* P (case x of C1 x1..xk => f1 x1..xk | ... | Cn => fn) = ((x = C1 x1..xk --> P (f1 x1..xk)) & ... & (x = Cn --> P fn)) *)

    val P_var = lthy9 |> yield_singleton (mk_Frees "P") (Ta --> HOLogic.boolT) |> fst

    (* Build LHS: P (case f1 ... fn x) *)
    val case_expr = list_comb (case_const, case_funs @ [x_ind])
    val lhs = P_var $ case_expr

    (* Build RHS: (ALL x1..xk. x = C1 x1..xk --> P (f1 x1..xk)) & ... *)
    fun mk_split_clause ((ctor, branch), arg_typs) =
      let
        val arg_vars = mk_Frees "a" arg_typs lthy9 |> fst
        val ctor_applied = list_comb (ctor, arg_vars)
        val branch_applied = list_comb (branch, arg_vars)
        val eq = HOLogic.mk_eq (x_ind, ctor_applied)
        val consequent = P_var $ branch_applied
        val body = HOLogic.mk_imp (eq, consequent)
      in
        fold_rev (fn v => fn b => HOLogic.mk_all (fst (dest_Free v), fastype_of v, abstract_over (v, b))) arg_vars body
      end

    val rhs_clauses = map mk_split_clause ((constr_terms ~~ case_funs) ~~ map snd constrs_with_typs)
    val rhs = foldr1 HOLogic.mk_conj rhs_clauses

    val split_prop = HOLogic.mk_eq (lhs, rhs) |> HOLogic.mk_Trueprop
    val split_vars = Variable.add_free_names lthy9 split_prop []

    val split_thm = trace_prove lthy9 split_vars [] split_prop
      (fn {context, ...} =>
        forward_split_tac context x_ind case_eq_thms exhaust_thm (map (length o snd) constrs_with_typs))

    fun mk_split_clause' ((ctor, branch), arg_typs) =
      let
        val arg_vars = mk_Frees "a" arg_typs lthy9 |> fst
        val ctor_applied = list_comb (ctor, arg_vars)
        val branch_applied = list_comb (branch, arg_vars)
        val eq = HOLogic.mk_eq (x_ind, ctor_applied)
        val consequent = P_var $ branch_applied |> HOLogic.mk_not
        val body = HOLogic.mk_conj (eq, consequent)
      in
        fold_rev (fn v => fn b => HOLogic.mk_exists (fst (dest_Free v), fastype_of v, abstract_over (v, b))) arg_vars body
      end

    val rhs_clauses' = map mk_split_clause' ((constr_terms ~~ case_funs) ~~ map snd constrs_with_typs)
    val rhs' = foldr1 HOLogic.mk_disj rhs_clauses' |> HOLogic.mk_not
    val split_asm_prop = HOLogic.mk_eq (lhs, rhs') |> HOLogic.mk_Trueprop
    val split_asm_thm = trace_prove lthy9 split_vars [] split_asm_prop
      (fn {context, ...} => solve_split_asm_tac context split_thm)

    val split_binding = Binding.qualify true typ_name (Binding.name "split")
    val split_asm_binding = Binding.qualify true typ_name (Binding.name "split_asm")
    val splits_binding = Binding.qualify true typ_name (Binding.name "splits")
    val lthy10 = lthy9
      |> Local_Theory.note ((split_binding, []), [split_thm])
      |> snd
      |> Local_Theory.note ((split_asm_binding, []), [split_asm_thm])
      |> snd
      |> Local_Theory.note ((splits_binding, []), [split_thm, split_asm_thm])
      |> snd
    val _ = timer "Split Theorem"

    val lthy11 = lthy10
      |> Local_Theory.background_theory
           (add_equal_instance typ constr_terms case_eq_thms
              (equal_eqns_by_rep typ rep_const Rep_inject rep_eqns))

  in
    lthy11
  end

(* Simplified enum command using natural number representation *)
fun enum_cmd_simpl (typ_binding, constrs : binding list) lthy =
  let
    val _ = if null constrs then error "Empty enum not allowed" else ()
    val time = timer lthy
    val timer = time (Timing.start ())
    val typ_name = Binding.name_of typ_binding
    val n = length constrs

    (* Step 1: Define the type using typedef over {..<n} *)
    val n_term = HOLogic.mk_nat n
    val typedef_set = @{Const\<open>lessThan HOLogic.natT for n_term\<close>}
    val timer = time (timer "Setup")

    val typedef_bindings = SOME {
      Abs_name = Binding.qualify true typ_name (Binding.name "Abs"),
      Rep_name = Binding.qualify true typ_name (Binding.name "Rep"),
      type_definition_name = Binding.qualify true typ_name (Binding.name "type_definition")
    }

    val ((_, (typ_info, typedef_info)), lthy1) = lthy
      |> Typedef.add_typedef {overloaded = false}
           (typ_binding, [], NoSyn) typedef_set typedef_bindings
           (fn ctxt => auto_tac ctxt)

    val { abs_type = typ, Abs_name, ...} = typ_info
    val abs_const = Const (Abs_name, HOLogic.natT --> typ)

    val {  Abs_induct, Abs_inject, ...} = typedef_info
    val timer = time (timer "Typedef")

    (* Step 2: Define constructors - each is just Abs i *)
    fun define_constructor c_binding (n, lthy) =
      let
        val constr_tm = abs_const $ n

        val qual_c_binding = Binding.qualify false typ_name c_binding
        val def_binding = Binding.qualify true typ_name (Binding.suffix_name "_def" c_binding)

        val ((trm, (_, def_thm)), lthy') = lthy
          |> Local_Theory.define ((qual_c_binding, NoSyn),
                                  ((def_binding, []), constr_tm))
        val phi = Local_Theory.target_morphism lthy'
        val trm = Morphism.term phi trm
        val def_thm = Morphism.thm phi def_thm
      in
        ((trm, def_thm), (HOLogic.mk_Suc n, lthy'))
      end

    val ((constr_terms, constr_defs), lthy2) = lthy1
      |> snd o Local_Theory.begin_nested
      |> pair HOLogic.zero
      |> fold_map define_constructor constrs
      ||> Local_Theory.end_nested o snd
      |>> split_list
    val timer = time (timer "Constructor Definitions")

    (* Step 3: Prove induction principle *)
    val ((P_ind, _), (x_ind, _)) =
      lthy2
      |> mk_Frees' "P" [typ --> HOLogic.boolT]
      |>> map_prod the_single the_single
      ||>> (mk_Frees' "x" [typ]
           #>> map_prod the_single the_single)
      |> fst

    val ind_prems = map (fn c => HOLogic.mk_Trueprop (P_ind $ c)) constr_terms
    val ind_concl = HOLogic.mk_Trueprop (P_ind $ x_ind)
    val ind_prop = Logic.list_implies (ind_prems, ind_concl)

    val vars = Variable.add_free_names lthy2 ind_prop []
    val induct_thm = trace_prove lthy2 vars [] ind_prop
      (fn {context, ...} =>
        EVERY [
          resolve_tac context [Abs_induct] 1 |> time_tactic "resolve" lthy2,
          rewrite_goal_tac context constr_defs 1 |> time_tactic "rewrite" lthy2,
          clarsimp_tac context 1 |> time_tactic "clarsimp" lthy2,
          (* Split on disjunctions from set membership *)
          REPEAT (etac context @{thm less_SucE} 1 THEN etac context @{thm HOL.ssubst} 2 THEN assume_tac context 2)
            |> time_tactic "repeat" lthy2, 
          TRY (simp_tac context 1) |> time_tactic "finale" lthy2
        ])
    val induct_binding = Binding.qualify true typ_name (Binding.name "induct")
    val constr_names = map Binding.name_of constrs
    val case_names_att = Attrib.internal \<^here> (fn _ => Rule_Cases.case_names constr_names)
    val (_, lthy3) = lthy2
      |> Local_Theory.note ((induct_binding, case_names_att :: @{attributes [induct type]}), [induct_thm])
    val timer = time (timer "Induction Principle")

    (* Step 4: Define case combinator *)
    (* case : 'a -> ... -> 'a -> typ -> 'a *)
    val (Ta, lthy4) = map_prod the_single I (mk_TFrees 1 lthy3)
    val case_arg_typs = replicate n Ta
    val case_typ = case_arg_typs ---> typ --> Ta

    val (case_branches, lthy5) = mk_Frees "f" case_arg_typs lthy4
    val prodTa = HOLogic.mk_prodT (typ, Ta)
    fun mk_case_list [] = @{Const\<open>Nil prodTa\<close>}
      | mk_case_list ((c, f) :: cfs) = @{Const\<open>Cons prodTa for \<open>HOLogic.mk_prod (c, f)\<close> \<open>mk_case_list cfs\<close>\<close>}

    (* the_map_of [(C1, f0), ..., (Cn, fn)] x *)
    val case_body = @{Const\<open>the_map_of typ Ta for \<open>mk_case_list (constr_terms ~~ case_branches)\<close> x_ind\<close>}
    val case_tm = fold_rev lambda case_branches (lambda x_ind case_body)

    val case_binding = Binding.qualify true typ_name (Binding.name "case")
    val case_def_binding = Binding.qualify true typ_name (Binding.name "case_def")

    val ((case_const, (_, case_def)), lthy6) = lthy5
      |> Local_Theory.define ((case_binding, NoSyn),
                              ((case_def_binding, []), case_tm))
    val phi = Local_Theory.target_morphism lthy6
    val case_const = Morphism.term phi case_const
    val case_const = Const (dest_Const_name case_const, case_typ)
    val case_def = Morphism.thm phi case_def

    (* Register with Case_Translation *)
    val lthy7 = lthy6
      |> Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
           (fn _ => Case_Translation.register case_const constr_terms)
    val timer = time (timer "Case expression")

    (* Step 5: Prove distinct theorems *)
    fun mk_distinct_thm idx =
      if idx = 0 then []
      else let
        val lower = 0 upto idx - 1
        val t = nth constr_terms idx
        val tdef = nth constr_defs idx
        fun pf j =
          let
            val t' = nth constr_terms j
            val neq = HOLogic.mk_eq (t, t') |> HOLogic.mk_not |> HOLogic.mk_Trueprop
            val t'def = nth constr_defs j
          in
            fn () => trace_prove lthy7 [] [] neq
              (fn {context, ...} => simp_tac (only_simpset context [Abs_inject, tdef, t'def, @{thm lessThan_iff}]) 1)
          end
      in
        map pf lower
      end
    val distinct_thms = maps mk_distinct_thm (1 upto n - 1) |> do_the_works lthy7
    val cases_binding = Binding.qualify true typ_name (Binding.name "distinct")
    val ((_, _), lthy8) = lthy7
      |> Local_Theory.note ((cases_binding, @{attributes [simp]}), distinct_thms)
    val timer = time (timer "Distinct")

    (* Step 6: Prove case equality theorems *)
    val case_eq_simp_thms = @{thms the_map_of_Cons_eq the_map_of_Cons_neq simp_thms} @ case_def :: distinct_thms
    fun mk_case_eq_thm (idx, c_term) =
      let
        val lhs = list_comb (case_const, case_branches @ [c_term])
        val fi = nth case_branches idx
        val eq = HOLogic.mk_eq (lhs, fi)
        val goal = fold_rev Logic.all case_branches (HOLogic.mk_Trueprop eq)
        val vars = Variable.add_free_names lthy8 goal []
      in
        fn () => trace_prove lthy8 vars [] goal
          (fn {context, ...} =>
            simp_tac (only_simpset context case_eq_simp_thms) 1 |> time_tactic "case simp" lthy8)
      end

    val case_eq_thms = 0 upto n - 1 ~~ constr_terms |> map mk_case_eq_thm |> do_the_works lthy8

    val cases_binding = Binding.qualify true typ_name (Binding.name "cases")
    val ((_, _), lthy9) = lthy8
      |> Local_Theory.note ((cases_binding, @{attributes [simp]}), case_eq_thms)
    val timer = time (timer "Case Equalities")

    (* Step 7: Prove exhaustiveness theorem *)
    val P = lthy9 |> Variable.variant_fixes ["P"] |> fst |> the_single |> (fn P => Free (P, HOLogic.boolT)) |> HOLogic.mk_Trueprop
    fun exhaust_case ctor =
      let
        val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (x_ind, ctor))
      in
        Logic.mk_implies (eq, P)
      end
    val premises = map exhaust_case constr_terms
    val goal = Logic.list_implies (premises, P)
    val vars = Variable.add_free_names lthy9 goal []
    val constr_names = map Binding.name_of constrs
    val (exhaust_thm, lthy10) =
      add_and_prove_exhaust lthy9 typ_name vars goal (fn ctxt => solve_exhaust_tac ctxt x_ind goal induct_thm) constr_names
    val timer = time (timer "Exhaustiveness")

    (* Step 8: Prove split theorems *)
    (* P (case x of C1 => f1 | ... | Cn => fn) = ((x = C1 --> P f1) & ... & (x = Cn --> P fn)) *)

    val P_var = lthy10 |> yield_singleton (mk_Frees "P") (Ta --> HOLogic.boolT) |> fst

    val case_expr = list_comb (case_const, case_branches @ [x_ind])
    val lhs = P_var $ case_expr

    fun mk_split_clause (ctor, branch) =
      let
        val eq = HOLogic.mk_eq (x_ind, ctor)
        val consequent = P_var $ branch
      in
        HOLogic.mk_imp (eq, consequent)
      end

    val rhs_clauses = map mk_split_clause (constr_terms ~~ case_branches)
    val rhs = foldr1 HOLogic.mk_conj rhs_clauses

    val split_prop = HOLogic.mk_eq (lhs, rhs) |> HOLogic.mk_Trueprop
    val split_vars = Variable.add_free_names lthy10 split_prop []

    val x_varc = Thm.cterm_of lthy10 x_ind
    val split_thm = trace_prove lthy10 split_vars [] split_prop
      (fn {context, ...} =>
        solve_split_tac context x_varc case_eq_thms exhaust_thm)

    fun mk_split_clause' (ctor, branch) =
      let
        val eq = HOLogic.mk_eq (x_ind, ctor)
        val consequent = P_var $ branch |> HOLogic.mk_not
      in
        HOLogic.mk_conj (eq, consequent)
      end

    val rhs_clauses' = map mk_split_clause' (constr_terms ~~ case_branches)
    val rhs' = foldr1 HOLogic.mk_disj rhs_clauses' |> HOLogic.mk_not
    val split_asm_prop = HOLogic.mk_eq (lhs, rhs') |> HOLogic.mk_Trueprop
    val split_asm_thm = trace_prove lthy10 split_vars [] split_asm_prop
      (fn {context, ...} => solve_split_asm_tac context split_thm)

    val split_binding = Binding.qualify true typ_name (Binding.name "split")
    val split_asm_binding = Binding.qualify true typ_name (Binding.name "split_asm")
    val splits_binding = Binding.qualify true typ_name (Binding.name "splits")
    val lthy11 = lthy10
      |> Local_Theory.note ((split_binding, []), [split_thm])
      |> snd
      |> Local_Theory.note ((split_asm_binding, []), [split_asm_thm])
      |> snd
      |> Local_Theory.note ((splits_binding, []), [split_thm, split_asm_thm])
      |> snd
    val _ = timer "Split Theorem"

    val lthy12 = lthy11
      |> add_and_prove_is_enum typ_name
      |> Local_Theory.background_theory
           (add_equal_instance typ constr_terms case_eq_thms
              (fn thy => let val (refl, eqns) = mk_equal_eqns typ constr_terms thy
                in (refl, false) :: map (rpair true) (rev eqns) end))

  in
    lthy12
  end

fun enum_cmd (typ_binding, constrs) lthy =
  let
    val time = timer lthy
    val timer = time (Timing.start ())
    
    val lthy' = if List.all (null o snd) constrs
      then enum_cmd_simpl (typ_binding, map fst constrs) lthy
      else enum_cmd_complex (typ_binding, constrs) lthy

    val _ = timer "Enum Complete"
  in
    lthy'
  end
end

(* Register the command *)
val _ =
  Outer_Syntax.local_theory @{command_keyword enum} "define enumeration type with proven theorems"
    (Parse.binding --
      (Parse.$$$ "=" |-- Parse.enum1 "|" (Parse.binding -- Scan.repeat Parse.typ))
     >> Enum_Cmd.enum_cmd)