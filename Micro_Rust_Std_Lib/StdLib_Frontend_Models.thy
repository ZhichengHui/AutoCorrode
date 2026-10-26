(*<*)
theory StdLib_Frontend_Models
  imports Crush.Crush StdLib_References StdLib_Slice
begin
(*>*)

section\<open>Models of standard library functions for translated Rust\<close>

text\<open>
  The Rust frontend (urust-frontend) translates a call of some Rust standard library functions to a
  call of a model of the function. The models below are written by hand: Rust's own definitions are
  not translated yet, and this library has no counterpart for them. A Rust \<^verbatim>\<open>Vec<T>\<close> and a
  slice \<^verbatim>\<open>[T]\<close> are values of type @{typ \<open>'v list\<close>} (their elements); a \<^verbatim>\<open>&mut\<close>
  reference to one is a reference to such a list. Undefined behaviour in Rust (e.g.
  \<^verbatim>\<open>get_unchecked\<close> out of bounds) aborts with a panic whose message starts with
  \<^verbatim>\<open>undefined behaviour\<close>, so that it is not mistaken for a Rust panic.
\<close>

text\<open>\<^verbatim>\<open>alloc::vec::from_elem(elem, n)\<close> (the expansion of \<^verbatim>\<open>vec![elem; n]\<close>): \<open>n\<close> copies of
  \<open>elem\<close>.\<close>
definition vec_from_elem :: \<open>'v \<Rightarrow> 64 word \<Rightarrow> ('s, 'v list, 'abort, 'i, 'o) function_body\<close> where
  \<open>vec_from_elem x n \<equiv> FunctionBody (literal (replicate (unat n) x))\<close>

text\<open>\<^verbatim>\<open><[T]>::get_unchecked(&self, i)\<close> with \<^verbatim>\<open>i: usize\<close>: the \<open>i\<close>-th element; out of
  bounds is undefined behaviour.\<close>
definition slice_get_unchecked :: \<open>'v list \<Rightarrow> 64 word \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_get_unchecked ls i \<equiv> FunctionBody (
     if unat i < length ls then literal (ls ! unat i)
     else abort (Panic (STR ''undefined behaviour: get_unchecked out of bounds'')))\<close>

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

text\<open>\<^verbatim>\<open><[T]>::get_unchecked_mut(&mut self, i)\<close> with \<^verbatim>\<open>i: usize\<close>: a reference to the
  \<open>i\<close>-th element; out of bounds is undefined behaviour.\<close>
definition slice_get_unchecked_mut :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, ('a, 'b, 'v) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_get_unchecked_mut ptr i \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>unat i < length ls\<rrangle> {
        return \<llangle>focus_nth (unat i) ptr\<rrangle>;
     };
     \<epsilon>\<open>abort (Panic (STR ''undefined behaviour: get_unchecked_mut out of bounds''))\<close>
  \<rbrakk>\<close>

no_adhoc_overloading store_update_const \<rightleftharpoons> update_fun

end

(*<*)
end
(*>*)
