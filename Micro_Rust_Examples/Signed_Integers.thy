(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Signed_Integers
  imports
    Micro_Rust_Std_Lib.StdLib_All
begin

section\<open>Verifying uRust programs on signed integers\<close>

text\<open>Signed integers have the types \<^typ>\<open>8 sword\<close>, \<^typ>\<open>16 sword\<close>, \<^typ>\<open>32 sword\<close> and
\<^typ>\<open>64 sword\<close> (\<^verbatim>\<open>i8\<close> to \<^verbatim>\<open>i64\<close>, \<^verbatim>\<open>isize\<close>). The uRust operators follow Rust's debug
semantics for them. Specifications use the signed readings \<^term>\<open>sint\<close>, \<^const>\<open>word_sless\<close> and \<^const>\<open>word_sle\<close>.\<close>

subsection\<open>Comparisons\<close>

definition clamp_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>clamp_i32 lo hi x \<equiv> FunctionBody \<lbrakk>
    if (x < lo) {
      lo
    } else {
      if (x > hi) {
        hi
      } else {
        x
      }
    }
  \<rbrakk>\<close>

definition clamp_i32_contract where
  \<open>clamp_i32_contract lo hi x \<equiv>
    let pre  = \<langle>lo \<le>s hi\<rangle> in
    let post = \<lambda>r. \<langle>lo \<le>s r \<and> r \<le>s hi\<rangle> in
    make_function_contract pre post\<close>

lemma clamp_i32_spec:
  shows \<open>\<Gamma>; clamp_i32 lo hi x \<Turnstile>\<^sub>F clamp_i32_contract lo hi x\<close>
  apply (crush_boot f: clamp_i32_def contract: clamp_i32_contract_def)
  apply (crush_base simp add: word_sle_eq word_sless_alt)
  done

definition max_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>max_i32 a b \<equiv> FunctionBody \<lbrakk>
    if (b > a) {
      b
    } else {
      a
    }
  \<rbrakk>\<close>

definition max_i32_contract where
  \<open>max_i32_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>sint r = max (sint a) (sint b)\<rangle> in
    make_function_contract pre post\<close>

lemma max_i32_spec:
  shows \<open>\<Gamma>; max_i32 a b \<Turnstile>\<^sub>F max_i32_contract a b\<close>
  apply (crush_boot f: max_i32_def contract: max_i32_contract_def)
  apply (crush_base simp add: word_sless_alt)
  done

subsection\<open>Arithmetic with overflow checks\<close>

text\<open>Addition panics unless the mathematical sum is in the range of \<^verbatim>\<open>i32\<close>.\<close>

definition add_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>add_i32 a b \<equiv> FunctionBody \<lbrakk> a + b \<rbrakk>\<close>

definition add_i32_contract where
  \<open>add_i32_contract a b \<equiv>
    let pre  = \<langle>- (2 ^ 31) \<le> sint a + sint b \<and> sint a + sint b < 2 ^ 31\<rangle> in
    let post = \<lambda>r. \<langle>r = a + b\<rangle> in
    make_function_contract pre post\<close>

lemma add_i32_spec:
  shows \<open>\<Gamma>; add_i32 a b \<Turnstile>\<^sub>F add_i32_contract a b\<close>
  apply (crush_boot f: add_i32_def contract: add_i32_contract_def)
  apply crush_base
  done

text\<open>Negation panics exactly on the minimum value.\<close>

definition negate_i32 :: \<open>32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>negate_i32 x \<equiv> FunctionBody \<lbrakk> -x \<rbrakk>\<close>

definition negate_i32_contract where
  \<open>negate_i32_contract x \<equiv>
    let pre  = \<langle>sint x \<noteq> - (2 ^ 31)\<rangle> in
    let post = \<lambda>r. \<langle>r = - x\<rangle> in
    make_function_contract pre post\<close>

lemma negate_i32_spec:
  shows \<open>\<Gamma>; negate_i32 x \<Turnstile>\<^sub>F negate_i32_contract x\<close>
  apply (crush_boot f: negate_i32_def contract: negate_i32_contract_def)
  apply (crush_base simp add: word_uminus_def)
  \<comment>\<open>The remaining goals are the bounds of \<^term>\<open>sint x\<close>, as with \<^verbatim>\<open>unat_lt2p\<close> for
    unsigned words.\<close>
  using sint_range'[of x] by auto

text\<open>Division truncates towards zero; it panics on division by zero and on the minimum value
divided by \<open>-1\<close>.\<close>

definition div_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>div_i32 a b \<equiv> FunctionBody \<lbrakk> a / b \<rbrakk>\<close>

definition div_i32_contract where
  \<open>div_i32_contract a b \<equiv>
    let pre  = \<langle>b \<noteq> 0 \<and> (sint a = - (2 ^ 31) \<longrightarrow> b \<noteq> -1)\<rangle> in
    let post = \<lambda>r. \<langle>r = a sdiv b\<rangle> in
    make_function_contract pre post\<close>

lemma div_i32_spec:
  shows \<open>\<Gamma>; div_i32 a b \<Turnstile>\<^sub>F div_i32_contract a b\<close>
  apply (crush_boot f: div_i32_def contract: div_i32_contract_def)
  apply crush_base
  done

subsection\<open>Casts\<close>

text\<open>Widening a signed integer preserves its value; widening an unsigned one zero-extends.\<close>

definition widen :: \<open>32 sword \<Rightarrow> 8 word \<Rightarrow> ('s, 64 sword \<times> 32 sword \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>widen x y \<equiv> FunctionBody \<lbrakk> (x as i64, y as i32) \<rbrakk>\<close>

definition widen_contract where
  \<open>widen_contract x y \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>sint (fst r) = sint x \<and> sint (fst (snd r)) = uint y\<rangle> in
    make_function_contract pre post\<close>

lemma widen_spec:
  shows \<open>\<Gamma>; widen x y \<Turnstile>\<^sub>F widen_contract x y\<close>
  apply (crush_boot f: widen_def contract: widen_contract_def)
  apply (crush_base simp add: sint_up_scast is_up)
  apply (simp add: sint_ucast_eq_uint is_down unsigned_ucast_eq)?
  done

end
