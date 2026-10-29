(*<*)
theory StdLib_Frontend_Models
  imports Crush.Crush StdLib_References
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

(*<*)
end
(*>*)
