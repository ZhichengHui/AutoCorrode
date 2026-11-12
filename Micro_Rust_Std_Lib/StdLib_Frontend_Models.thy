(*<*)
theory StdLib_Frontend_Models
  imports Crush.Crush StdLib_References
  keywords "urust_const_data" :: thy_defn
begin
(*>*)

section\<open>Models of standard library functions for translated Rust\<close>

text\<open>
  The Rust frontend (urust-frontend) translates a call of some Rust standard library functions to a
  call of a model of the function. The models below are written by hand: Rust's own definitions are
  not translated yet, and this library has no counterpart for them. A Rust \<^verbatim>\<open>Vec<T>\<close> and a
  slice \<^verbatim>\<open>[T]\<close> are values of type @{typ \<open>'v list\<close>} (their elements); a \<^verbatim>\<open>&mut\<close>
  reference to one is a reference to such a list.
\<close>

text\<open>\<^verbatim>\<open>alloc::vec::from_elem(elem, n)\<close> (the expansion of \<^verbatim>\<open>vec![elem; n]\<close>): \<open>n\<close> copies of
  \<open>elem\<close>.\<close>
definition vec_from_elem :: \<open>'v \<Rightarrow> 64 word \<Rightarrow> ('s, 'v list, 'abort, 'i, 'o) function_body\<close> where
  \<open>vec_from_elem x n \<equiv> FunctionBody (literal (replicate (unat n) x))\<close>

definition vec_from_elem_contract :: \<open>'v \<Rightarrow> 64 word \<Rightarrow> ('s::sepalg, 'v list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>vec_from_elem_contract x n \<equiv>
     let pre = emp in
     let post = \<lambda>r. \<langle>r = replicate (unat n) x\<rangle> in
       make_function_contract pre post\<close>

lemma vec_from_elem_spec [crush_specs]:
  shows \<open>\<Gamma> ; vec_from_elem x n \<Turnstile>\<^sub>F vec_from_elem_contract x n\<close>
  by (crush_boot f: vec_from_elem_def contract: vec_from_elem_contract_def) crush_base

context reference
begin

adhoc_overloading store_update_const \<rightleftharpoons> update_fun

text\<open>\<^verbatim>\<open>Vec::push(&mut self, x)\<close>: appends \<open>x\<close>.\<close>
definition vec_push :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_push ptr x \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     ptr = \<llangle>ls @ [x]\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Vec::pop(&mut self)\<close>: removes the last element and returns it; \<^verbatim>\<open>None\<close> if empty.\<close>
definition vec_pop :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow>
      ('s, 'v option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_pop ptr \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>ls = []\<rrangle> {
        return None;
     };
     ptr = \<llangle>butlast ls\<rrangle>;
     \<llangle>Some (last ls)\<rrangle>
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open><[T]>::swap(&mut self, a, b)\<close>: exchanges the \<open>a\<close>-th and \<open>b\<close>-th elements; panics if
  either is out of bounds.\<close>
definition slice_swap :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_swap ptr a b \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>unat a < length ls \<and> unat b < length ls\<rrangle> {
        ptr = \<llangle>ls[unat a := ls ! unat b, unat b := ls ! unat a]\<rrangle>;
        ()
     } else {
        panic!("index out of bounds")
     }
  \<rbrakk>\<close>

no_adhoc_overloading store_update_const \<rightleftharpoons> update_fun

end

section\<open>Type variables of a definition's body only\<close>

text\<open>
  A type variable that occurs in the right-hand side of a definition \<open>c \<equiv> t\<close> but not in the
  type of \<open>c\<close> is not constrained by anything: the program never observes a value of that type
  (for instance the element type of an empty list that is only measured, or the value type of a
  \<^verbatim>\<open>return\<close> ending a loop body). Isabelle would make it an extra \<^typ>\<open>'a itself\<close>
  parameter of \<open>c\<close>, so that no use of \<open>c\<close> at its stated type type-checks. With the option
  \<open>urust_ground_body_types\<close> (set by the theories the frontend generates) such schematic type
  variables are instantiated with \<^typ>\<open>unit\<close> after type inference.
\<close>

ML\<open>
val urust_ground_body_types = Attrib.setup_config_bool \<^binding>\<open>urust_ground_body_types\<close> (K false);

fun urust_ground_body_type_vars ctxt ts =
  if not (Config.get ctxt urust_ground_body_types) then ts
  else
    let
      (*the type variables of the context's fixed variables, e.g. of a locale's parameters*)
      val context_tfrees =
        Vartab.fold (fn (_, T) => Term.add_tfreesT T) (#1 (Variable.constraints_of ctxt)) []
      fun ground (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ lhs $ rhs) t =
            let
              val stated = fastype_of lhs
              val tvars = subtract (op =) (Term.add_tvarsT stated []) (Term.add_tvars rhs [])
              val tfrees = subtract (op =) (Term.add_tfreesT stated context_tfrees) (Term.add_tfrees rhs [])
              val unit_for = (fn v => (v, \<^typ>\<open>unit\<close>))
            in
              t |> Term_Subst.instantiate (TVars.make (map unit_for tvars), Vars.empty)
                |> Term_Subst.instantiate_frees (TFrees.make (map unit_for tfrees), Frees.empty)
            end
        | ground _ t = t
    in map (fn t => ground t t) ts end;

val _ = Context.>> (Syntax_Phases.term_check 100 "urust_ground_body_types" urust_ground_body_type_vars);
\<close>

text\<open>A Rust constant with a large value (for instance a lookup table of 10^5 entries) is
  translated from the value computed by Rust's constant evaluation, with

  \<^verbatim>\<open>urust_const_data "c" :: \<open>T\<close> = \<open>data\<close>\<close>

  which defines \<open>c \<equiv> FunctionBody (literal v)\<close> of type \<open>T\<close>, a \<^typ>\<open>('s, 'v, 'abort, 'i, 'o) function_body\<close>.
  The value \<open>v :: 'v\<close> is given by \<open>data\<close>:
  \<^item> an integer, possibly negative, a numeral of the expected type;
  \<^item> \<open>name\<close> or \<open>name(d1, .., dn)\<close>, the constant \<open>name\<close> applied to the values \<open>d1\<close>, .., \<open>dn\<close>;
  \<^item> \<open>[d1, .., dn]\<close>, a list; \<open>()\<close>, the unit; \<open>(d1, .., dn)\<close> for \<open>n \<ge> 2\<close>, a tuple.
  The term is built in one pass over the data, from the expected type down: the inner syntax
  (parsing and type inference) takes time superlinear in the size of such a term, and does not
  finish for tables of this size. Only the small term \<open>FunctionBody (literal x)\<close> is checked.\<close>

ML\<open>
structure Urust_Const_Data =
struct

datatype data = Int of int | App of string * data list | List of data list | Tuple of data list

fun parse s =
  let
    val n = size s
    val pos = Unsynchronized.ref 0
    fun peek () = if ! pos < n then SOME (String.sub (s, ! pos)) else NONE
    fun advance () = pos := ! pos + 1
    fun skip_ws () = (case peek () of SOME c => if Char.isSpace c then (advance (); skip_ws ()) else () | NONE => ())
    fun err msg = error ("urust_const_data: " ^ msg ^ " at offset " ^ string_of_int (! pos))
    fun expect c = (skip_ws (); if peek () = SOME c then advance () else err ("expected " ^ quote (str c)))
    fun is_name_char c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'" orelse c = #"."
    fun take_while p =
      let val start = ! pos
          fun go () = (case peek () of SOME c => if p c then (advance (); go ()) else () | NONE => ())
      in go (); String.substring (s, start, ! pos - start) end
    fun digits () =
      let val ds = take_while Char.isDigit
      in if ds = "" then err "expected digits"
         else fold (fn c => fn acc => acc * 10 + (Char.ord c - Char.ord #"0")) (String.explode ds) 0 end
    fun value () =
      (skip_ws ();
       case peek () of
         SOME #"[" => List (seq #"[" #"]")
       | SOME #"(" =>
           (case seq #"(" #")" of
              [] => Tuple []
            | [_] => err "a tuple has at least two components"
            | ds => Tuple ds)
       | SOME #"-" => (advance (); Int (~ (digits ())))
       | SOME c =>
           if Char.isDigit c then Int (digits ())
           else if is_name_char c then
             let val name = take_while is_name_char
             in skip_ws (); if peek () = SOME #"(" then App (name, seq #"(" #")") else App (name, []) end
           else err ("unexpected " ^ quote (str c))
       | NONE => err "unexpected end")
    and seq opn cls =
      let
        val _ = expect opn
        fun more acc =
          let val d = value () in
            skip_ws ();
            (case peek () of
              SOME c => if c = #"," then (advance (); more (d :: acc))
                        else if c = cls then (advance (); rev (d :: acc))
                        else err ("expected " ^ quote "," ^ " or " ^ quote (str cls))
            | NONE => err "unexpected end")
          end
      in skip_ws (); if peek () = SOME cls then (advance (); []) else more [] end
    val d = value ()
  in skip_ws (); if ! pos < n then err "trailing text" else d end

(*the term of type T given by d*)
fun elaborate ctxt T d =
  let
    val thy = Proof_Context.theory_of ctxt
    val consts = Unsynchronized.ref Symtab.empty
    fun const name =
      (case Symtab.lookup (! consts) name of
        SOME c => c
      | NONE =>
          let val c = Proof_Context.read_const {proper = true, strict = true} ctxt name
          in consts := Symtab.update (name, c) (! consts); c end)
    fun bad T what = error ("urust_const_data: " ^ what ^ " for the type " ^ Syntax.string_of_typ ctxt T)
    fun elab T (Int i) = HOLogic.mk_number T i
      | elab T (List ds) =
          (case T of
            Type (\<^type_name>\<open>list\<close>, [A]) => HOLogic.mk_list A (map (elab A) ds)
          | _ => bad T "a list")
      | elab T (Tuple []) = if T = HOLogic.unitT then HOLogic.unit else bad T "()"
      | elab T (Tuple [d]) = elab T d
      | elab T (Tuple (d :: ds)) =
          (case T of
            Type (\<^type_name>\<open>prod\<close>, [A, B]) => HOLogic.mk_prod (elab A d, elab B (Tuple ds))
          | _ => bad T "a tuple")
      | elab T (App (name, ds)) =
          let
            val (c, cT) = dest_Const (const name)
            val k = length ds
            val argTs = take k (binder_types cT)
            val _ = if length argTs = k then () else error ("urust_const_data: too many arguments of " ^ quote name)
            val resT = funpow k range_type cT
            val tyenv = Sign.typ_match thy (resT, T) Vartab.empty
              handle Type.TYPE_MATCH => bad T ("the constant " ^ quote name ^ " of type " ^ Syntax.string_of_typ ctxt cT)
            val inst = Envir.subst_type tyenv
          in list_comb (Const (c, inst cT), map2 (fn A => elab (inst A)) argTs ds) end
  in elab T d end

fun const_data ((b, raw_T), raw_data) lthy =
  let
    val T = Syntax.read_typ lthy raw_T
    val vT =
      (case T of
        Type (\<^type_name>\<open>function_body\<close>, [_, vT, _, _, _]) => vT
      | _ => error "urust_const_data: the type is not a function_body type")
    val v = elaborate lthy vT (parse raw_data)
    val x = Free ("x", vT)
    val template = Syntax.check_term lthy
      (Type.constraint T (Const (\<^const_name>\<open>FunctionBody\<close>, dummyT) $ (Const (\<^const_name>\<open>literal\<close>, dummyT) $ x)))
    val rhs = Term.subst_free [(x, v)] template
  in
    lthy |> Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), rhs)) |> snd
  end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>urust_const_data\<close>
    "define a uRust constant by its value, built from data without the inner syntax"
    (Parse.binding -- (\<^keyword>\<open>::\<close> |-- Parse.typ) -- (\<^keyword>\<open>=\<close> |-- Parse.embedded) >> const_data)

end
\<close>

(*<*)
end
(*>*)
