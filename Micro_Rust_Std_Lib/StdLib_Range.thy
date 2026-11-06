(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Range                            
  imports Crush.Crush Shallow_Micro_Rust.Range_Type
begin
(*>*)

text\<open>Ranges are ranges of words. Their bounds are compared as signed words if the length type is
signed (\<^const>\<open>word_rust_lt\<close>, \<^const>\<open>word_rust_le\<close>).\<close>

definition is_empty_contract :: \<open>'l::len word range \<Rightarrow> ('machine::{sepalg}, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>is_empty_contract r \<equiv>
    let pre  = emp;
        post = \<lambda>res. \<langle>res \<longleftrightarrow>
          (if end_inclusive r then word_rust_lt (end r) (start r) else \<not> word_rust_lt (start r) (end r))\<rangle>
     in make_function_contract pre post\<close>

lemma is_empty_spec [crush_specs]:
  shows \<open>\<Gamma> ; is_empty r \<Turnstile>\<^sub>F is_empty_contract r\<close>
by (contract f: is_empty_def contract: is_empty_contract_def) crush_base

definition contains_contract :: \<open>'l::len word range \<Rightarrow> 'l word \<Rightarrow> ('machine::{sepalg}, bool, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>contains_contract r e \<equiv>
    let pre  = emp;
        post = \<lambda>res. \<langle>res \<longleftrightarrow>
          (if end_inclusive r then word_rust_le (start r) e \<and> word_rust_le e (end r)
           else word_rust_le (start r) e \<and> word_rust_lt e (end r))\<rangle>
     in make_function_contract pre post\<close>

lemma contains_spec [crush_specs]:  
  shows \<open>\<Gamma> ; contains r e \<Turnstile>\<^sub>F contains_contract r e\<close>
by (contract f: contains_def contract: contains_contract_def) crush_base

text\<open>A signed range enumerates the signed values from the start in increasing order. The rule
branches on the signedness instead of assuming it, so that it applies without side conditions.\<close>

lemma range_into_list_make_range [micro_rust_simps]:
  fixes s e :: \<open>'l::len word\<close>
  shows \<open>range_into_list (make_range s e incl) =
    (if is_signed TYPE('l) then
       (if incl then list.map word_of_int [sint s..sint e]
        else list.map word_of_int [sint s..sint e - 1])
     else if incl then list.map word_of_nat [unat s..<Suc (unat e)]
     else list.map word_of_nat [unat s..<unat e])\<close>
by (clarsimp simp add: range_into_list_def)

(*<*)
end
(*>*)
