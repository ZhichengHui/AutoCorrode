(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Ordering
  imports Crush.Crush StdLib_References Misc.Result
begin
(*>*)

datatype ordering
  = Less
  | Equal
  | Greater
micro_rust_notation (literal) ordering.Less ("Ordering::Less")
micro_rust_notation (literal) ordering.Equal ("Ordering::Equal")
micro_rust_notation (literal) ordering.Greater ("Ordering::Greater")

text\<open>\<^verbatim>\<open>cmp\<close> compares words, as signed words if the length type is signed
(\<^const>\<open>word_rust_lt\<close>).\<close>

definition cmp_pure :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ordering\<close> where
  \<open>cmp_pure x y \<equiv>
     if word_rust_lt x y then
       Less
     else if x = y then
       Equal
     else Greater\<close>

definition cmp :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s, ordering, 'abort, 'i, 'o) function_body\<close> where
  \<open>cmp \<equiv> lift_fun2 cmp_pure\<close>

text\<open>\<^const>\<open>cmp_pure\<close> follows the signedness of the length type and is unfolded into its uses
at concrete word lengths for code generation (see \<^verbatim>\<open>Signedness\<close>).\<close>

declare cmp_pure_def[abs_def, code_unfold] cmp_def[abs_def, code_unfold]

(*<*)
end
(*>*)