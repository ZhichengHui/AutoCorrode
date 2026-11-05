(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Signed_Tests_Automation
  imports
    Micro_Rust_Std_Lib.StdLib_All
begin

section\<open>Tests of the reasoning side of signed integers\<close>

text\<open>Every signed test is placed next to its unsigned analogue. The unsigned analogue checks that
the premises added to the unsigned rules did not change what the automation can do.\<close>

subsection\<open>Concrete facts about signed words used below\<close>

text\<open>Sanity checks on the underlying word operations (these document Rust's semantics and
serve as counterexamples for wrong specifications).\<close>

lemma sword_facts:
  shows \<open>sint (100 :: 8 sword) = 100\<close>
    and \<open>sint ((100 :: 8 sword) + 100) = -56\<close>
    and \<open>sint (-128 :: 8 sword) = -128\<close>
    and \<open>(-7 :: 8 sword) sdiv 2 = -3\<close>
    and \<open>(-7 :: 8 sword) smod 2 = -1\<close>
    and \<open>(7 :: 8 sword) sdiv (-2) = -3\<close>
    and \<open>(7 :: 8 sword) smod (-2) = 1\<close>
    and \<open>(-128 :: 8 sword) sdiv (-1) = -128\<close>
    and \<open>signed_drop_bit 1 (-7 :: 8 sword) = -4\<close>
    and \<open>signed_drop_bit 7 (-128 :: 8 sword) = -1\<close>
    and \<open>drop_bit 1 (249 :: 8 word) = 124\<close>
    and \<open>(scast (-1 :: 8 sword) :: 32 word) = 4294967295\<close>
    and \<open>(scast (-1 :: 8 sword) :: 32 sword) = -1\<close>
    and \<open>sint (ucast (200 :: 8 word) :: 32 sword) = 200\<close>
    and \<open>(scast (300 :: 32 sword) :: 8 sword) = 44\<close>
    and \<open>(-5 :: 8 sword) <s 3\<close>
  by simp_all

text\<open>Wrong readings are refuted on concrete instances: a signed division is not an unsigned one,
rounding is towards zero, and the unsigned sum does not wrap into the signed result.\<close>

context notes [[urust_signed_order_check = false]] begin
lemma sword_counterexamples:
  shows \<open>(-7 :: 8 sword) div 2 \<noteq> (-7 :: 8 sword) sdiv 2\<close>
    and \<open>(-7 :: 8 sword) sdiv 2 \<noteq> -4\<close>
    and \<open>(-7 :: 8 sword) smod 2 \<noteq> 1\<close>
    and \<open>\<not> ((-5 :: 8 sword) < 3)\<close>
    and \<open>sint ((100 :: 8 sword) + 100) \<noteq> 200\<close>
    and \<open>unat ((100 :: 8 sword) + 100) = 200\<close>
    and \<open>drop_bit 1 (-8 :: 8 sword) \<noteq> signed_drop_bit 1 (-8 :: 8 sword)\<close>
  by simp_all
end

subsection\<open>Evaluation rules (Eval.thy)\<close>

text\<open>The signed rules at concrete types; the premise \<^term>\<open>is_signed TYPE(8 signed)\<close> must be
discharged by the simplifier on its own.\<close>

lemma eval_add_i8_overflow:
  fixes x y :: \<open>8 sword\<close>
  assumes \<open>x = 100\<close> and \<open>y = 100\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {}\<close>
  using assms by (simp_all add: urust_eval_action_add_no_wrap_signed)

lemma eval_add_i8_ok:
  fixes x y :: \<open>8 sword\<close>
  assumes \<open>x = 100\<close> and \<open>y = 27\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(127, \<sigma>)}\<close>
    and \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {}\<close>
  using assms by (simp_all add: urust_eval_action_add_no_wrap_signed)

lemma eval_add_i8_negative_overflow:
  fixes x y :: \<open>8 sword\<close>
  assumes \<open>x = -128\<close> and \<open>y = -1\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x + y \<rbrakk>\<rangle> (Panic overflow_err_msg, \<sigma>)\<close>
    and \<open>\<not> (\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x + y \<rbrakk>\<rangle> (v, \<sigma>'))\<close>
  using assms by (simp_all add: urust_eval_predicate_add_no_wrap_signed)

text\<open>Using the collective rule set, which contains the unsigned and the signed rule.\<close>

lemma eval_add_i8_via_set:
  fixes x y :: \<open>8 sword\<close>
  assumes \<open>x = 100\<close> and \<open>y = 100\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
  using assms by (simp add: urust_eval_action_simps)

lemma eval_add_u8_regression:
  fixes x y :: \<open>8 word\<close>
  assumes \<open>x = 200\<close> and \<open>y = 100\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>((\<Gamma>, \<lbrakk> x + 55 \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(255, \<sigma>)}\<close>
  using assms by (simp_all add: urust_eval_action_add_no_wrap)

lemma eval_add_u8_via_set:
  fixes x y :: \<open>8 word\<close>
  assumes \<open>x = 200\<close> and \<open>y = 100\<close>
  shows \<open>((\<Gamma>, \<lbrakk> x + y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
  using assms by (simp add: urust_eval_action_simps)

lemma eval_add_u64_regression:
  fixes x y :: \<open>64 word\<close>
  assumes \<open>x = 2^63\<close> and \<open>y = 2^63\<close>
  shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x + y \<rbrakk>\<rangle> (Panic overflow_err_msg, \<sigma>)\<close>
  using assms by (simp add: urust_eval_predicate_add_no_wrap)

lemma eval_mul_i8:
  fixes x y :: \<open>8 sword\<close>
  shows \<open>x = -128 \<Longrightarrow> y = -1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>x = 16 \<Longrightarrow> y = 8 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {}\<close>
    and \<open>x = -16 \<Longrightarrow> y = 8 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(-128, \<sigma>)}\<close>
    and \<open>x = -16 \<Longrightarrow> y = 8 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x * y \<rbrakk>\<rangle> (-128, \<sigma>)\<close>
  by (simp_all add: urust_eval_action_mul_no_wrap_signed urust_eval_predicate_mul_no_wrap_signed)

lemma eval_mul_u8_regression:
  fixes x y :: \<open>8 word\<close>
  shows \<open>x = 16 \<Longrightarrow> y = 16 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>x = 16 \<Longrightarrow> y = 8 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x * y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(128, \<sigma>)}\<close>
  by (simp_all add: urust_eval_action_mul_no_wrap)

lemma eval_sub_i8:
  fixes x y :: \<open>8 sword\<close>
  shows \<open>x = -128 \<Longrightarrow> y = 1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x - y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>x = 0 \<Longrightarrow> y = -128 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x - y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>x = 3 \<Longrightarrow> y = 5 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x - y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(-2, \<sigma>)}\<close>
    and \<open>x = 3 \<Longrightarrow> y = 5 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x - y \<rbrakk>\<rangle> (-2, \<sigma>)\<close>
  by (simp_all add: urust_eval_action_sub_no_wrap_signed urust_eval_predicate_sub_no_wrap_signed)

lemma eval_sub_u8_regression:
  fixes x y :: \<open>8 word\<close>
  shows \<open>x = 3 \<Longrightarrow> y = 5 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x - y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>x = 5 \<Longrightarrow> y = 3 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x - y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(2, \<sigma>)}\<close>
    and \<open>x = 5 \<Longrightarrow> y = 3 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x - y \<rbrakk>\<rangle> (2, \<sigma>)\<close>
  by (simp_all add: urust_eval_action_sub_no_wrap urust_eval_predicate_sub_no_wrap)

lemma eval_div_i8:
  fixes x y :: \<open>8 sword\<close>
  shows \<open>x = -7 \<Longrightarrow> y = 2 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x / y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(-3, \<sigma>)}\<close>
    and \<open>x = 7 \<Longrightarrow> y = -2 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x / y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(-3, \<sigma>)}\<close>
    and \<open>x = -128 \<Longrightarrow> y = -1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x / y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>x = -128 \<Longrightarrow> y = -1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x / y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {}\<close>
    and \<open>x = 5 \<Longrightarrow> y = 0 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x / y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic (String.implode ''division by zero''), \<sigma>)}\<close>
    and \<open>x = -7 \<Longrightarrow> y = 2 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x / y \<rbrakk>\<rangle> (-3, \<sigma>)\<close>
    and \<open>x = -128 \<Longrightarrow> y = -1 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x / y \<rbrakk>\<rangle> (Panic overflow_err_msg, \<sigma>)\<close>
    and \<open>x = 5 \<Longrightarrow> y = 0 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x / y \<rbrakk>\<rangle> (Panic (String.implode ''division by zero''), \<sigma>)\<close>
  by (simp_all add: urust_eval_action_div_signed urust_eval_predicate_div_signed)

lemma eval_div_u8_regression:
  fixes x y :: \<open>8 word\<close>
  shows \<open>x = 7 \<Longrightarrow> y = 2 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x / y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(3, \<sigma>)}\<close>
    and \<open>x = 7 \<Longrightarrow> y = 0 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x / y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic (String.implode ''division by zero''), \<sigma>)}\<close>
    and \<open>x = 7 \<Longrightarrow> y = 2 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x / y \<rbrakk>\<rangle> (3, \<sigma>)\<close>
  by (simp_all add: urust_eval_action_div urust_eval_predicate_div)

lemma eval_mod_i8:
  fixes x y :: \<open>8 sword\<close>
  shows \<open>x = -7 \<Longrightarrow> y = 2 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x % y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(-1, \<sigma>)}\<close>
    and \<open>x = 7 \<Longrightarrow> y = -2 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x % y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(1, \<sigma>)}\<close>
    and \<open>x = -128 \<Longrightarrow> y = -1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x % y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>x = 5 \<Longrightarrow> y = 0 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x % y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic (String.implode ''division by zero''), \<sigma>)}\<close>
    and \<open>x = -7 \<Longrightarrow> y = 2 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x % y \<rbrakk>\<rangle> (-1, \<sigma>)\<close>
    and \<open>x = -128 \<Longrightarrow> y = -1 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x % y \<rbrakk>\<rangle> (Panic overflow_err_msg, \<sigma>)\<close>
  by (simp_all add: urust_eval_action_mod_signed urust_eval_predicate_mod_signed)

lemma eval_mod_u8_regression:
  fixes x y :: \<open>8 word\<close>
  shows \<open>x = 7 \<Longrightarrow> y = 2 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x % y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(1, \<sigma>)}\<close>
    and \<open>x = 7 \<Longrightarrow> y = 2 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x % y \<rbrakk>\<rangle> (1, \<sigma>)\<close>
  by (simp_all add: urust_eval_action_mod urust_eval_predicate_mod)

lemma eval_shr_i8:
  fixes x :: \<open>8 sword\<close> and y :: \<open>64 word\<close>
  shows \<open>x = -8 \<Longrightarrow> y = 1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x >> y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(-4, \<sigma>)}\<close>
    and \<open>x = -128 \<Longrightarrow> y = 7 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x >> y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(-1, \<sigma>)}\<close>
    and \<open>x = -1 \<Longrightarrow> y = 8 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x >> y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>x = -8 \<Longrightarrow> y = 1 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x >> y \<rbrakk>\<rangle> (-4, \<sigma>)\<close>
    and \<open>x = -1 \<Longrightarrow> y = 8 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> x >> y \<rbrakk>\<rangle> (Panic overflow_err_msg, \<sigma>)\<close>
  by (simp_all add: urust_eval_action_shift_right_signed urust_eval_predicate_shift_right_signed)

lemma eval_shr_u8_regression:
  fixes x :: \<open>8 word\<close> and y :: \<open>64 word\<close>
  shows \<open>x = 248 \<Longrightarrow> y = 1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x >> y \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(124, \<sigma>)}\<close>
    and \<open>x = 1 \<Longrightarrow> y = 8 \<Longrightarrow> ((\<Gamma>, \<lbrakk> x >> y \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>x = 248 \<Longrightarrow> y = 1 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x >> y \<rbrakk>\<rangle> (124, \<sigma>)\<close>
  by (simp_all add: urust_eval_action_shift_right urust_eval_predicate_shift_right)

lemma eval_uminus_i8:
  fixes x :: \<open>8 sword\<close>
  shows \<open>x = -128 \<Longrightarrow> ((\<Gamma>, \<lbrakk> -x \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>x = 5 \<Longrightarrow> ((\<Gamma>, \<lbrakk> -x \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(-5, \<sigma>)}\<close>
    and \<open>x = -127 \<Longrightarrow> ((\<Gamma>, \<lbrakk> -x \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(127, \<sigma>)}\<close>
    and \<open>x = 5 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> -x \<rbrakk>\<rangle> (-5, \<sigma>)\<close>
    and \<open>x = -128 \<Longrightarrow> \<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, \<lbrakk> -x \<rbrakk>\<rangle> (Panic overflow_err_msg, \<sigma>)\<close>
  by (simp_all add: urust_eval_action_uminus_signed urust_eval_predicate_uminus_signed)

text\<open>The rules also apply at the other signed widths.\<close>

lemma eval_add_i32_i64:
  fixes a b :: \<open>32 sword\<close> and c d :: \<open>64 sword\<close>
  shows \<open>a = 2^31 - 1 \<Longrightarrow> b = 1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> a + b \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>c = 2^63 - 1 \<Longrightarrow> d = 1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> c + d \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>c = -(2^63) \<Longrightarrow> d = -1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> c / d \<rbrakk>) \<diamondop>\<^sub>a \<sigma>) = {(Panic overflow_err_msg, \<sigma>)}\<close>
    and \<open>a = -(2^31) \<Longrightarrow> b = 2^31 - 1 \<Longrightarrow> ((\<Gamma>, \<lbrakk> a + b \<rbrakk>) \<diamondop>\<^sub>v \<sigma>) = {(-1, \<sigma>)}\<close>
  by (simp_all add: urust_eval_action_add_no_wrap_signed urust_eval_action_div_signed)

text\<open>Symbolic (non-concrete) consequences of the rules.\<close>

lemma eval_add_signed_symbolic:
  fixes x y :: \<open>'l::len word\<close>
  assumes \<open>is_signed TYPE('l)\<close>
      and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x + y \<rbrakk>\<rangle> (v, \<sigma>')\<close>
    shows \<open>sint v = sint x + sint y\<close>
  using assms by (simp add: urust_eval_predicate_add_no_wrap_signed sint_word_ariths signed_take_bit_int_eq_self)

lemma eval_div_signed_symbolic:
  fixes x y :: \<open>32 sword\<close>
  assumes \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, \<lbrakk> x / y \<rbrakk>\<rangle> (v, \<sigma>')\<close>
    shows \<open>y \<noteq> 0\<close> and \<open>v = x sdiv y\<close>
  using assms by (simp_all add: urust_eval_predicate_div_signed)

subsection\<open>Literal comparison and shift rules (Numeric\_Types\_Lemmas.thy)\<close>

lemma lt_literal_signed_i32:
  fixes c d :: \<open>32 sword\<close>
  shows \<open>\<lbrakk> c < d \<rbrakk> = \<lbrakk> \<llangle>c <s d\<rrangle> \<rbrakk>\<close>
    and \<open>\<lbrakk> c > d \<rbrakk> = \<lbrakk> \<llangle>d <s c\<rrangle> \<rbrakk>\<close>
    and \<open>\<lbrakk> c >= d \<rbrakk> = \<lbrakk> \<llangle>d \<le>s c\<rrangle> \<rbrakk>\<close>
    and \<open>\<lbrakk> c <= d \<rbrakk> = \<lbrakk> \<llangle>c \<le>s d\<rrangle> \<rbrakk>\<close>
  by (simp_all add: evaluate_lt_literal_signed evaluate_gt_literal_signed
    evaluate_ge_literal_signed evaluate_le_literal_signed)

lemma lt_literal_signed_i32_via_simps:
  fixes c d :: \<open>32 sword\<close>
  shows \<open>\<lbrakk> c < d \<rbrakk> = \<lbrakk> \<llangle>c <s d\<rrangle> \<rbrakk>\<close>
    and \<open>\<lbrakk> c <= d \<rbrakk> = \<lbrakk> \<llangle>c \<le>s d\<rrangle> \<rbrakk>\<close>
  by (simp_all add: micro_rust_simps)

lemma lt_literal_unsigned_u32_regression:
  fixes c d :: \<open>32 word\<close>
  shows \<open>\<lbrakk> c < d \<rbrakk> = \<lbrakk> \<llangle>c < d\<rrangle> \<rbrakk>\<close>
    and \<open>\<lbrakk> c > d \<rbrakk> = \<lbrakk> \<llangle>d < c\<rrangle> \<rbrakk>\<close>
    and \<open>\<lbrakk> c >= d \<rbrakk> = \<lbrakk> \<llangle>d \<le> c\<rrangle> \<rbrakk>\<close>
    and \<open>\<lbrakk> c <= d \<rbrakk> = \<lbrakk> \<llangle>c \<le> d\<rrangle> \<rbrakk>\<close>
  by (simp_all add: evaluate_lt_literal evaluate_gt_literal evaluate_ge_literal evaluate_le_literal)

lemma lt_literal_unsigned_u32_via_simps:
  fixes c d :: \<open>32 word\<close>
  shows \<open>\<lbrakk> c < d \<rbrakk> = \<lbrakk> \<llangle>c < d\<rrangle> \<rbrakk>\<close>
  by (simp add: micro_rust_simps)

lemma shift_right_literal_signed_i32:
  fixes c :: \<open>32 sword\<close> and d :: \<open>64 word\<close>
  assumes \<open>unat d < 32\<close>
  shows \<open>\<lbrakk> c >> d \<rbrakk> = \<lbrakk> \<llangle>signed_drop_bit (unat d) c\<rrangle> \<rbrakk>\<close>
  using assms by (simp add: evaluate_word_shift_right_literal_signed)

lemma shift_right_literal_unsigned_u32_regression:
  fixes c :: \<open>32 word\<close> and d :: \<open>64 word\<close>
  assumes \<open>unat d < 32\<close>
  shows \<open>\<lbrakk> c >> d \<rbrakk> = \<lbrakk> \<llangle>drop_bit (unat d) c\<rrangle> \<rbrakk>\<close>
  using assms by (simp add: evaluate_word_shift_right_literal)

subsection\<open>Triples (Triple.thy, Weak\_Triple.thy)\<close>

lemma sstriple_signed_i32:
  fixes x y :: \<open>32 sword\<close> and s :: \<open>64 word\<close>
  shows \<open>\<Gamma> ; \<langle>- (2 ^ 31) \<le> sint x + sint y \<and> sint x + sint y < 2 ^ 31\<rangle> \<turnstile> \<lbrakk> x + y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x + y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>- (2 ^ 31) \<le> sint x * sint y \<and> sint x * sint y < 2 ^ 31\<rangle> \<turnstile> \<lbrakk> x * y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x * y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>- (2 ^ 31) \<le> sint x - sint y \<and> sint x - sint y < 2 ^ 31\<rangle> \<turnstile> \<lbrakk> x - y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x - y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>y \<noteq> 0 \<and> (sint x = - (2 ^ 31) \<longrightarrow> y \<noteq> -1)\<rangle> \<turnstile> \<lbrakk> x / y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x sdiv y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>y \<noteq> 0 \<and> (sint x = - (2 ^ 31) \<longrightarrow> y \<noteq> -1)\<rangle> \<turnstile> \<lbrakk> x % y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x smod y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>unat s < 32\<rangle> \<turnstile> \<lbrakk> x >> s \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = signed_drop_bit (unat s) x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using sstriple_word_add_no_wrap_signedI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    sstriple_word_mul_no_wrap_signedI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    sstriple_word_sub_no_wrap_signedI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    sstriple_word_udiv_signedI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    sstriple_word_umod_signedI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    sstriple_word_shift_right_signedI[where x = x and y = s and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
  by simp_all

lemma sstriple_unsigned_u32_regression:
  fixes x y :: \<open>32 word\<close> and s :: \<open>64 word\<close>
  shows \<open>\<Gamma> ; \<langle>unat x + unat y < 2 ^ 32\<rangle> \<turnstile> \<lbrakk> x + y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x + y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>unat x * unat y < 2 ^ 32\<rangle> \<turnstile> \<lbrakk> x * y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x * y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>y \<le> x\<rangle> \<turnstile> \<lbrakk> x - y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x - y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>y \<noteq> 0\<rangle> \<turnstile> \<lbrakk> x / y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x div y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>y \<noteq> 0\<rangle> \<turnstile> \<lbrakk> x % y \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = x mod y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>unat s < 32\<rangle> \<turnstile> \<lbrakk> x >> s \<rbrakk> \<stileturn> (\<lambda>r. \<langle>r = drop_bit (unat s) x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using sstriple_word_add_no_wrapI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    sstriple_word_mul_no_wrapI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    sstriple_word_sub_no_wrapI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    sstriple_word_udivI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    sstriple_word_umodI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    sstriple_word_shift_rightI[where x = x and y = s and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
  by simp_all

lemma striple_signed_i8:
  fixes x y :: \<open>8 sword\<close> and s :: \<open>64 word\<close>
  shows \<open>\<Gamma> ; \<langle>- (2 ^ 7) \<le> sint x + sint y \<and> sint x + sint y < 2 ^ 7\<rangle> \<turnstile> \<lbrakk> x + y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x + y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>- (2 ^ 7) \<le> sint x * sint y \<and> sint x * sint y < 2 ^ 7\<rangle> \<turnstile> \<lbrakk> x * y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x * y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>- (2 ^ 7) \<le> sint x - sint y \<and> sint x - sint y < 2 ^ 7\<rangle> \<turnstile> \<lbrakk> x - y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x - y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>y \<noteq> 0 \<and> (sint x = - (2 ^ 7) \<longrightarrow> y \<noteq> -1)\<rangle> \<turnstile> \<lbrakk> x / y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x sdiv y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>y \<noteq> 0 \<and> (sint x = - (2 ^ 7) \<longrightarrow> y \<noteq> -1)\<rangle> \<turnstile> \<lbrakk> x % y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x smod y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>unat s < 8\<rangle> \<turnstile> \<lbrakk> x >> s \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = signed_drop_bit (unat s) x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using striple_word_add_no_wrap_signedI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    striple_word_mul_no_wrap_signedI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    striple_word_sub_no_wrap_signedI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    striple_word_udiv_signedI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    striple_word_umod_signedI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    striple_word_shift_right_signedI[where x = x and y = s and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
  by simp_all

lemma striple_unsigned_u8_regression:
  fixes x y :: \<open>8 word\<close> and s :: \<open>64 word\<close>
  shows \<open>\<Gamma> ; \<langle>unat x + unat y < 2 ^ 8\<rangle> \<turnstile> \<lbrakk> x + y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x + y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>y \<le> x\<rangle> \<turnstile> \<lbrakk> x - y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x - y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>y \<noteq> 0\<rangle> \<turnstile> \<lbrakk> x / y \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = x div y\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
    and \<open>\<Gamma> ; \<langle>unat s < 8\<rangle> \<turnstile> \<lbrakk> x >> s \<rbrakk> \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>r. \<langle>r = drop_bit (unat s) x\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using striple_word_add_no_wrapI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    striple_word_sub_no_wrapI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    striple_word_udivI[where x = x and y = y and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    striple_word_shift_rightI[where x = x and y = s and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
  by simp_all

subsection\<open>Weakest preconditions (Weakest\_Precondition.thy)\<close>

text\<open>Crush simplifies with \<^verbatim>\<open>micro_rust_simps\<close> alone, so these must reduce the signedness
branches on their own.\<close>

lemma micro_rust_simps_reduce_is_signed:
  shows \<open>(if is_signed TYPE(32 signed) then P else Q) = P\<close>
    and \<open>(if is_signed TYPE(32) then P else Q) = Q\<close>
    and \<open>(if is_signed TYPE(64 signed) then P else Q) = P\<close>
    and \<open>(if is_signed TYPE(8) then P else Q) = Q\<close>
    and \<open>(if is_signed TYPE(1) then P else Q) = Q\<close>
    and \<open>word_rust_lt (a :: 16 sword) b = (a <s b)\<close>
    and \<open>word_rust_le (a :: 16 sword) b = (a \<le>s b)\<close>
    and \<open>word_rust_lt (c :: 16 word) d = (c < d)\<close>
    and \<open>word_rust_le (c :: 16 word) d = (c \<le> d)\<close>
    and \<open>(word_rust_cast (a :: 16 sword) :: 64 word) = scast a\<close>
    and \<open>(word_rust_cast (c :: 16 word) :: 64 sword) = ucast c\<close>
    and \<open>(word_rust_cast :: 16 sword \<Rightarrow> 8 sword) = scast\<close>
    and \<open>(word_rust_cast :: 16 word \<Rightarrow> 8 sword) = ucast\<close>
  by (simp_all only: micro_rust_simps)

text\<open>The intro forms as Crush applies them: after the rule, the remaining entailment has the
conditional precondition, which \<^verbatim>\<open>micro_rust_simps\<close> alone must reduce.\<close>

lemma wp_intros_signed_i32:
  fixes x y :: \<open>32 sword\<close> and s :: \<open>64 word\<close>
  shows \<open>\<langle>- (2 ^ 31) \<le> sint x + sint y \<and> sint x + sint y < 2 ^ 31\<rangle> \<star> \<psi> (x + y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x + y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>- (2 ^ 31) \<le> sint x * sint y \<and> sint x * sint y < 2 ^ 31\<rangle> \<star> \<psi> (x * y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x * y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>- (2 ^ 31) \<le> sint x - sint y \<and> sint x - sint y < 2 ^ 31\<rangle> \<star> \<psi> (x - y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x - y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>y \<noteq> 0 \<and> (sint x = - (2 ^ 31) \<longrightarrow> y \<noteq> -1)\<rangle> \<star> \<psi> (x sdiv y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x / y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>y \<noteq> 0 \<and> (sint x = - (2 ^ 31) \<longrightarrow> y \<noteq> -1)\<rangle> \<star> \<psi> (x smod y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x % y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>unat s < 32\<rangle> \<star> \<psi> (signed_drop_bit (unat s) x) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x >> s \<rbrakk> \<psi> \<rho> \<theta>\<close>
  by (rule wp_word_add_no_wrapI wp_word_mul_no_wrapI wp_word_sub_no_wrapI wp_word_udivI
    wp_word_umodI wp_word_shift_rightI; simp add: micro_rust_simps aentails_refl)+

lemma wp_intros_unsigned_u32_regression:
  fixes x y :: \<open>32 word\<close> and s :: \<open>64 word\<close>
  shows \<open>\<langle>unat x + unat y < 2 ^ 32\<rangle> \<star> \<psi> (x + y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x + y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>unat x * unat y < 2 ^ 32\<rangle> \<star> \<psi> (x * y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x * y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>y \<le> x\<rangle> \<star> \<psi> (x - y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x - y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x div y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x / y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x mod y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x % y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>unat s < 32\<rangle> \<star> \<psi> (drop_bit (unat s) x) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x >> s \<rbrakk> \<psi> \<rho> \<theta>\<close>
  by (rule wp_word_add_no_wrapI wp_word_mul_no_wrapI wp_word_sub_no_wrapI wp_word_udivI
    wp_word_umodI wp_word_shift_rightI; simp add: micro_rust_simps aentails_refl)+

text\<open>The signed and unsigned auxiliaries directly.\<close>

lemma wp_aux_signed_i64:
  fixes x y :: \<open>64 sword\<close> and s :: \<open>64 word\<close>
  shows \<open>\<langle>- (2 ^ 63) \<le> sint x + sint y \<and> sint x + sint y < 2 ^ 63\<rangle> \<star> \<psi> (x + y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x + y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>- (2 ^ 63) \<le> sint x * sint y \<and> sint x * sint y < 2 ^ 63\<rangle> \<star> \<psi> (x * y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x * y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>- (2 ^ 63) \<le> sint x - sint y \<and> sint x - sint y < 2 ^ 63\<rangle> \<star> \<psi> (x - y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x - y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>y \<noteq> 0 \<and> (sint x = - (2 ^ 63) \<longrightarrow> y \<noteq> -1)\<rangle> \<star> \<psi> (x sdiv y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x / y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>y \<noteq> 0 \<and> (sint x = - (2 ^ 63) \<longrightarrow> y \<noteq> -1)\<rangle> \<star> \<psi> (x smod y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x % y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>unat s < 64\<rangle> \<star> \<psi> (signed_drop_bit (unat s) x) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x >> s \<rbrakk> \<psi> \<rho> \<theta>\<close>
  using wp_word_add_no_wrap_signed[where x = x and y = y and \<psi> = \<psi> and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    wp_word_mul_no_wrap_signed[where x = x and y = y and \<psi> = \<psi> and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    wp_word_sub_no_wrap_signed[where x = x and y = y and \<psi> = \<psi> and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    wp_word_udiv_signed[where x = x and y = y and \<psi> = \<psi> and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    wp_word_umod_signed[where x = x and y = y and \<psi> = \<psi> and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    wp_word_shift_right_signed[where x = x and y = s and \<psi> = \<psi> and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
  by simp_all

lemma wp_aux_unsigned_u64:
  fixes x y :: \<open>64 word\<close> and s :: \<open>64 word\<close>
  shows \<open>\<langle>unat x + unat y < 2 ^ 64\<rangle> \<star> \<psi> (x + y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x + y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>y \<le> x\<rangle> \<star> \<psi> (x - y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x - y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>y \<noteq> 0\<rangle> \<star> \<psi> (x div y) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x / y \<rbrakk> \<psi> \<rho> \<theta>\<close>
    and \<open>\<langle>unat s < 64\<rangle> \<star> \<psi> (drop_bit (unat s) x) \<longlongrightarrow> \<W>\<P> \<Gamma> \<lbrakk> x >> s \<rbrakk> \<psi> \<rho> \<theta>\<close>
  using wp_word_add_no_wrap_unsigned[where x = x and y = y and \<psi> = \<psi> and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    wp_word_sub_no_wrap_unsigned[where x = x and y = y and \<psi> = \<psi> and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    wp_word_udiv_unsigned[where x = x and y = y and \<psi> = \<psi> and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
    wp_word_shift_right_unsigned[where x = x and y = s and \<psi> = \<psi> and \<Gamma> = \<Gamma> and \<rho> = \<rho> and \<theta> = \<theta>]
  by simp_all

subsection\<open>Signed word lemmas (WordAdditional.thy)\<close>

lemma wa_lt_sword_to_intI:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>sint a < sint b \<Longrightarrow> a <s b\<close>
  by (erule lt_sword_to_intI)

lemma wa_sint_mono:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>a <s b \<Longrightarrow> sint a < sint b\<close>
  by (erule sint_mono)

lemma wa_lt_sword_to_intE:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>a <s b \<Longrightarrow> sint a < sint b\<close>
  by (erule lt_sword_to_intE, assumption)

lemma wa_sint_ucast_eq_concrete:
  shows \<open>sint (word_of_int 100 :: 8 sword) = 100\<close>
    and \<open>sint (word_of_int (-128) :: 8 sword) = -128\<close>
    and \<open>sint (word_of_int (2^31 - 1) :: 32 sword) = 2^31 - 1\<close>
  by (simp_all add: sint_ucast_eq)

lemma wa_sint_ucast_eq_bad_input:
  \<comment>\<open>Out of range, the rule does not apply (its premises fail); the value wraps.\<close>
  shows \<open>sint (word_of_int 128 :: 8 sword) = -128\<close>
  by simp

lemma wa_sword_sint_lt:
  shows \<open>(word_of_int (-3) :: 8 sword) <s word_of_int 5\<close>
    and \<open>(word_of_int (-128) :: 8 sword) <s word_of_int 127\<close>
    and \<open>(word_of_int (-5) :: 32 sword) <s word_of_int (-4)\<close>
  by (rule sword_sint_lt; simp)+

lemma wa_sint_weaken:
  fixes x x' :: \<open>32 sword\<close>
  shows \<open>x <s x' \<Longrightarrow> sint x' \<le> 10 \<Longrightarrow> sint x < 10\<close>
    and \<open>x \<le>s x' \<Longrightarrow> sint x' \<le> 10 \<Longrightarrow> sint x \<le> 10\<close>
  by (erule (1) sint_lt_weakenI, erule (1) sint_le_weakenI)

lemma wa_sint_ucast_adjoint:
  fixes x :: \<open>8 sword\<close>
  shows \<open>sint x < 100 \<longleftrightarrow> x <s word_of_int 100\<close>
    and \<open>sint x < -100 \<longleftrightarrow> x <s word_of_int (-100)\<close>
  by (rule sint_ucast_adjoint; simp)+

lemma wa_sword_range_sorted:
  shows \<open>sorted_wrt (\<le>s) (List.map (word_of_int :: int \<Rightarrow> 8 sword) [-100..100 - 1])\<close>
  by (rule sword_range_sorted; simp)

lemma wa_add_sword_lessI:
  fixes a c :: \<open>8 sword\<close>
  assumes \<open>a + word_of_int 10 <s c\<close> \<open>-100 \<le> sint a\<close> \<open>sint a < 100\<close>
  shows \<open>a + word_of_int 3 <s c\<close>
  by (rule add_sword_lessI[where b = 10 and n = 3]) (use assms in simp_all)

lemma wa_set_of_swordlist:
  shows \<open>set (List.map word_of_int [-3..3 - 1]) = {v :: 8 sword. word_of_int (-3) \<le>s v \<and> v <s word_of_int 3}\<close>
  by (rule set_of_swordlist; simp)

lemma wa_set_of_swordlist_concrete1:
  shows \<open>(-1 :: 8 sword) \<in> set (List.map word_of_int [-3..3 - 1])\<close>
  by (subst set_of_swordlist) (simp_all add: word_sle_eq word_sless_alt)

lemma wa_set_of_swordlist_concrete2:
  shows \<open>(3 :: 8 sword) \<notin> set (List.map word_of_int [-3..3 - 1])\<close>
  by (subst set_of_swordlist) (simp_all add: word_sle_eq word_sless_alt)

lemma wa_sint_sword_comparison:
  fixes x :: \<open>32 sword\<close>
  assumes \<open>sint x = y\<close>
  shows \<open>x = word_of_int y\<close> \<open>- (2 ^ 31) \<le> y\<close> \<open>y < 2 ^ 31\<close>
  using sint_sword_comparison[OF assms] by simp_all

lemma wa_sint_sword_comparisonE:
  fixes x :: \<open>32 sword\<close>
  assumes \<open>sint x = y\<close>
  shows \<open>y < 2 ^ 31\<close>
  using assms by (elim sint_sword_comparisonE) simp

lemma wa_sword_int_bound:
  fixes v :: \<open>16 sword\<close>
  assumes \<open>v \<le>s word_of_int 1000\<close>
  shows \<open>sint v \<le> 1000\<close> and \<open>v = word_of_int (sint v)\<close>
  using sword_int_bound[OF assms] by simp_all

lemma wa_sword_int_bound':
  fixes v :: \<open>16 sword\<close>
  shows \<open>v \<le>s word_of_int (-1000) \<longleftrightarrow> sint v \<le> -1000\<close>
  by (rule sword_int_bound'; simp)

lemma wa_sword_int_boundE:
  fixes v :: \<open>16 sword\<close>
  assumes \<open>v \<le>s word_of_int 1000\<close>
  shows \<open>sint v \<le> 1000\<close>
  using assms by (elim sword_int_boundE) simp_all

lemma wa_sint_sword_of_int64:
  fixes w :: \<open>64 sword\<close>
  shows \<open>sint w \<le> 5 \<Longrightarrow> w \<le>s word_of_int 5\<close>
    and \<open>sint w < -5 \<Longrightarrow> w <s word_of_int (-5)\<close>
  by (erule sint_sword_of_int64_le, simp, erule sint_sword_of_int64_less, simp)

lemma wa_le_sint_soi':
  fixes z :: \<open>8 sword\<close>
  assumes \<open>-100 < sint z\<close>
  shows \<open>sint (word_of_int (-100) :: 8 sword) = -100\<close>
  using assms by (intro le_sint_soi'[where z = z]) simp_all

lemma wa_image_sword_of_int:
  shows \<open>word_of_int ` {-3..<3} = {w :: 8 sword. word_of_int (-3) \<le>s w \<and> w <s word_of_int 3}\<close>
    and \<open>word_of_int ` {-3..3} = {w :: 8 sword. word_of_int (-3) \<le>s w \<and> w \<le>s word_of_int 3}\<close>
  by (rule image_sword_of_int_atLeastLessThan image_sword_of_int_atLeastAtMost; simp)+

lemma wa_image_sint:
  fixes a b :: \<open>8 sword\<close>
  shows \<open>sint ` {w. a \<le>s w \<and> w <s b} = {sint a..<sint b}\<close>
    and \<open>sint ` {w. a \<le>s w \<and> w \<le>s b} = {sint a..sint b}\<close>
  by (rule image_sint_atLeastLessThan image_sint_atLeastAtMost)+

lemma wa_lt_sub_left_sword:
  fixes x y :: \<open>32 sword\<close>
  shows \<open>0 <s x \<Longrightarrow> x <s y \<Longrightarrow> y - x <s y\<close>
  by (rule lt_sub_left_sword)

text\<open>The attributes: the intro and elim rules are collected in \<^verbatim>\<open>word_nat_intros\<close> and
\<^verbatim>\<open>word_nat_elims\<close>, and \<^verbatim>\<open>sint_ucast_eq\<close> is a \<^verbatim>\<open>word_nat_simps\<close> rule.\<close>

lemma wa_attributes:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>sint a < sint b \<Longrightarrow> a <s b\<close>
    and \<open>a <s b \<Longrightarrow> sint a < sint b\<close>
    and \<open>sint (word_of_int 100 :: 8 sword) = 100\<close>
  by (rule word_nat_intros, assumption, erule word_nat_elims, assumption, simp add: word_nat_simps)

subsection\<open>Specification check\<close>

text\<open>Negative cases: HOL's unsigned readings on signed words are rejected at parse time.\<close>

ML\<open>
local
  val ctxt = \<^context>;
  fun rejected s =
    (case Exn.capture (Syntax.read_term ctxt) s of
      Exn.Exn e => String.isSubstring "Unsigned reading of a signed word" (Runtime.exn_message e)
    | Exn.Res _ => false);
  fun accepted s = can (Syntax.read_term ctxt) s;
in
  val _ = \<^assert> (rejected "(a :: 32 sword) < b");
  val _ = \<^assert> (rejected "(a :: 32 sword) \<le> b");
  val _ = \<^assert> (rejected "(a :: 32 sword) > b");
  val _ = \<^assert> (rejected "(a :: 8 sword) div b");
  val _ = \<^assert> (rejected "(a :: 64 sword) mod b");
  val _ = \<^assert> (rejected "min (a :: 32 sword) b");
  val _ = \<^assert> (rejected "max (a :: 32 sword) b");
  val _ = \<^assert> (rejected "Max (S :: 32 sword set)");
  val _ = \<^assert> (rejected "Min (S :: 32 sword set)");
  val _ = \<^assert> (rejected "{(a :: 32 sword)..b}");
  val _ = \<^assert> (rejected "{(a :: 32 sword)..<b}");
  val _ = \<^assert> (rejected "{(a :: 32 sword)<..b}");
  val _ = \<^assert> (rejected "{(a :: 32 sword)<..<b}");
  val _ = \<^assert> (rejected "{..(a :: 32 sword)}");
  val _ = \<^assert> (rejected "{..<(a :: 32 sword)}");
  val _ = \<^assert> (rejected "{(a :: 32 sword)..}");
  val _ = \<^assert> (rejected "{(a :: 32 sword)<..}");
  val _ = \<^assert> (rejected "sorted (xs :: 32 sword list)");
  (* Positive cases. *)
  val _ = \<^assert> (accepted "(a :: 32 sword) <s b");
  val _ = \<^assert> (accepted "(A :: 32 sword set) \<subseteq> B");
  val _ = \<^assert> (accepted "(A :: 32 sword set) \<subset> B");
  \<comment>\<open>Derived orders are not checked (only direct uses at a signed word are).\<close>
  val _ = \<^assert> (accepted "(f :: nat \<Rightarrow> 32 sword) \<le> g");
  val _ = \<^assert> (accepted "(a :: 32 sword) \<le>s b");
  val _ = \<^assert> (accepted "sint (a :: 32 sword) < sint b");
  val _ = \<^assert> (accepted "sint (a :: 32 sword) \<le> 5");
  val _ = \<^assert> (accepted "(a :: 32 sword) sdiv b");
  val _ = \<^assert> (accepted "(a :: 32 sword) smod b");
  val _ = \<^assert> (accepted "max (sint (a :: 32 sword)) (sint b)");
  val _ = \<^assert> (accepted "min (sint (a :: 32 sword)) (sint b)");
  val _ = \<^assert> (accepted "{sint (a :: 32 sword)..sint b}");
  val _ = \<^assert> (accepted "{sint (a :: 32 sword)..<sint b}");
  val _ = \<^assert> (accepted "sint (a :: 32 sword) div 2");
  val _ = \<^assert> (accepted "(a :: 32 word) < b");
  val _ = \<^assert> (accepted "(a :: 32 word) div b");
  val _ = \<^assert> (accepted "min (a :: 64 word) b");
  val _ = \<^assert> (accepted "{(a :: 8 word)..b}");
  val _ = \<^assert> (accepted "(n :: nat) < m");
  val _ = \<^assert> (accepted "(n :: int) \<le> m");
  val _ = \<^assert> (accepted "length (xs :: 32 sword list) < n");
  val _ = \<^assert> (accepted "(f :: 32 sword \<Rightarrow> nat) x < n");
  val _ = \<^assert> (accepted "unat (a :: 32 sword) < unat b");
  val _ = \<^assert> (accepted "{w :: 32 sword. a \<le>s w \<and> w <s b}");
  val _ = \<^assert> (accepted "sint ` {w :: 32 sword. a \<le>s w \<and> w <s b} = {sint a..<sint b}");
  val _ = \<^assert> (accepted "word_of_int ` {a..<b} = {w :: 32 sword. word_of_int a \<le>s w \<and> w <s word_of_int b}");
end
\<close>

text\<open>The check also applies to terms in lemma statements, including those of other sessions:
the statement below is the one of \<^verbatim>\<open>sword_range_sorted\<close> in \<^verbatim>\<open>WordAdditional\<close>.\<close>

text\<open>Regression: \<^const>\<open>sorted_wrt\<close> with the signed order is accepted.\<close>

lemma sorted_wrt_sle_statement_accepted:
  shows \<open>sorted_wrt (\<le>s) (List.map (word_of_int :: int \<Rightarrow> 8 sword) [-100..100 - 1])\<close>
  by (rule sword_range_sorted; simp)
ML\<open>\<^assert> (can (Syntax.read_term \<^context>) "sorted_wrt (\<le>s) (xs :: 32 sword list)")\<close>
ML\<open>\<^assert> (not (can (Syntax.read_term \<^context>) "sorted (xs :: 32 sword list)"))\<close>

text\<open>The check can be disabled in a context.\<close>

context notes [[urust_signed_order_check = false]] begin
ML\<open>\<^assert> (can (Syntax.read_term \<^context>) "(a :: 32 sword) < b")\<close>
ML\<open>\<^assert> (can (Syntax.read_term \<^context>) "sorted_wrt (\<le>s) (xs :: 32 sword list)")\<close>
lemma \<open>(0 :: 8 sword) < 1\<close> by simp
end

text\<open>And it is active again afterwards.\<close>

ML\<open>\<^assert> (not (can (Syntax.read_term \<^context>) "(a :: 32 sword) < b"))\<close>

text\<open>The check does not interfere with \<open>sint\<close>-based contracts in this theory, which were all
accepted above; and the mixed cases in the generic contracts (\<open>word_rust_lt\<close>) are accepted.\<close>

ML\<open>\<^assert> (can (Syntax.read_term \<^context>) "word_rust_lt (a :: 32 sword) b")\<close>

subsection\<open>Crush on pure order goals\<close>

lemma crush_order_sword:
  fixes a b c :: \<open>16 sword\<close>
  shows \<open>a <s b \<Longrightarrow> sint a < sint b\<close>
    and \<open>a <s b \<Longrightarrow> b \<le>s a \<Longrightarrow> False\<close>
  by crush_base+

lemma crush_order_word_regression:
  fixes a b c :: \<open>16 word\<close>
  shows \<open>a < b \<Longrightarrow> unat a < unat b\<close>
    and \<open>a < b \<Longrightarrow> b \<le> a \<Longrightarrow> False\<close>
  by crush_base+

text\<open>Chains of two order facts are beyond \<^verbatim>\<open>crush_base\<close> for unsigned and signed words alike
(the word bound tactic derives one consequence per premise); both need the same kind of hint.\<close>

lemma crush_order_sword_hinted:
  fixes a b c :: \<open>16 sword\<close>
  shows \<open>a <s b \<Longrightarrow> b <s c \<Longrightarrow> sint a < sint c\<close>
    and \<open>a \<le>s b \<Longrightarrow> b <s c \<Longrightarrow> sint a < sint c\<close>
    and \<open>a <s b \<Longrightarrow> sint b \<le> 10 \<Longrightarrow> sint a < 10\<close>
    and \<open>a <s b \<Longrightarrow> sint a + 1 \<le> sint b\<close>
  by (crush_base simp add: word_sless_alt word_sle_eq)+

lemma crush_order_word_hinted:
  fixes a b c :: \<open>16 word\<close>
  shows \<open>a < b \<Longrightarrow> b < c \<Longrightarrow> unat a < unat c\<close>
    and \<open>a \<le> b \<Longrightarrow> b < c \<Longrightarrow> unat a < unat c\<close>
    and \<open>a < b \<Longrightarrow> unat b \<le> 10 \<Longrightarrow> unat a < 10\<close>
  by (crush_base simp add: word_less_nat_alt word_le_nat_alt)+

lemma crush_sword_sint_lt:
  shows \<open>(word_of_int (-3) :: 8 sword) <s word_of_int 5\<close>
    and \<open>(word_of_int (-128) :: 8 sword) <s word_of_int 0\<close>
  by crush_base+

lemma crush_word_unat_lt_regression:
  shows \<open>(word_of_nat 3 :: 8 word) < word_of_nat 5\<close>
  by crush_base

subsection\<open>Crush end-to-end: arithmetic\<close>

definition add_i8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> ('s, 8 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>add_i8 a b \<equiv> FunctionBody \<lbrakk> a + b \<rbrakk>\<close>

definition add_i8_contract where
  \<open>add_i8_contract a b \<equiv>
    let pre  = \<langle>- 128 \<le> sint a + sint b \<and> sint a + sint b < 128\<rangle> in
    let post = \<lambda>r. \<langle>r = a + b \<and> sint r = sint a + sint b\<rangle> in
    make_function_contract pre post\<close>

text\<open>The value-level postcondition \<open>sint r = sint a + sint b\<close> needs the word arithmetic lemmas
as a hint; the unsigned analogue needs the corresponding \<open>unat\<close> lemma.\<close>

lemma add_i8_spec:
  shows \<open>\<Gamma>; add_i8 a b \<Turnstile>\<^sub>F add_i8_contract a b\<close>
  by (crush_boot f: add_i8_def contract: add_i8_contract_def)
    (crush_base simp add: sint_word_ariths signed_take_bit_int_eq_self)

definition add_u8 :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> ('s, 8 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>add_u8 a b \<equiv> FunctionBody \<lbrakk> a + b \<rbrakk>\<close>

definition add_u8_contract where
  \<open>add_u8_contract a b \<equiv>
    let pre  = \<langle>unat a + unat b < 256\<rangle> in
    let post = \<lambda>r. \<langle>r = a + b \<and> unat r = unat a + unat b\<rangle> in
    make_function_contract pre post\<close>

lemma add_u8_spec:
  shows \<open>\<Gamma>; add_u8 a b \<Turnstile>\<^sub>F add_u8_contract a b\<close>
  by (crush_boot f: add_u8_def contract: add_u8_contract_def)
    (crush_base simp add: unat_add_lem')

definition arith_i16 :: \<open>16 sword \<Rightarrow> 16 sword \<Rightarrow> ('s, 16 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>arith_i16 a b \<equiv> FunctionBody \<lbrakk> (a - b) * 2_i16 \<rbrakk>\<close>

definition arith_i16_contract where
  \<open>arith_i16_contract a b \<equiv>
    let pre  = \<langle>- (2 ^ 14) \<le> sint a - sint b \<and> sint a - sint b < 2 ^ 14\<rangle> in
    let post = \<lambda>r. \<langle>r = (a - b) * 2\<rangle> in
    make_function_contract pre post\<close>

lemma arith_i16_spec:
  shows \<open>\<Gamma>; arith_i16 a b \<Turnstile>\<^sub>F arith_i16_contract a b\<close>
  by (crush_boot f: arith_i16_def contract: arith_i16_contract_def)
    (crush_base simp add: sint_word_ariths signed_take_bit_int_eq_self)

definition arith_u16 :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow> ('s, 16 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>arith_u16 a b \<equiv> FunctionBody \<lbrakk> (a - b) * 2_u16 \<rbrakk>\<close>

definition arith_u16_contract where
  \<open>arith_u16_contract a b \<equiv>
    let pre  = \<langle>b \<le> a \<and> unat a - unat b < 2 ^ 15\<rangle> in
    let post = \<lambda>r. \<langle>r = (a - b) * 2\<rangle> in
    make_function_contract pre post\<close>

lemma arith_u16_spec:
  shows \<open>\<Gamma>; arith_u16 a b \<Turnstile>\<^sub>F arith_u16_contract a b\<close>
  by (crush_boot f: arith_u16_def contract: arith_u16_contract_def)
    (crush_base simp add: unat_sub)

definition mul_i64 :: \<open>64 sword \<Rightarrow> 64 sword \<Rightarrow> ('s, 64 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>mul_i64 a b \<equiv> FunctionBody \<lbrakk> a * b \<rbrakk>\<close>

definition mul_i64_contract where
  \<open>mul_i64_contract a b \<equiv>
    let pre  = \<langle>- (2 ^ 63) \<le> sint a * sint b \<and> sint a * sint b < 2 ^ 63\<rangle> in
    let post = \<lambda>r. \<langle>sint r = sint a * sint b\<rangle> in
    make_function_contract pre post\<close>

lemma mul_i64_spec:
  shows \<open>\<Gamma>; mul_i64 a b \<Turnstile>\<^sub>F mul_i64_contract a b\<close>
  by (crush_boot f: mul_i64_def contract: mul_i64_contract_def)
    (crush_base simp add: sint_word_ariths signed_take_bit_int_eq_self)

definition mul_u64 :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>mul_u64 a b \<equiv> FunctionBody \<lbrakk> a * b \<rbrakk>\<close>

definition mul_u64_contract where
  \<open>mul_u64_contract a b \<equiv>
    let pre  = \<langle>unat a * unat b < 2 ^ 64\<rangle> in
    let post = \<lambda>r. \<langle>unat r = unat a * unat b\<rangle> in
    make_function_contract pre post\<close>

lemma mul_u64_spec:
  shows \<open>\<Gamma>; mul_u64 a b \<Turnstile>\<^sub>F mul_u64_contract a b\<close>
  by (crush_boot f: mul_u64_def contract: mul_u64_contract_def)
    (crush_base simp add: unat_mult_lem[THEN iffD1])

text\<open>Division and remainder with the \<open>MIN / -1\<close> precondition.\<close>

definition divrem_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, 32 sword \<times> 32 sword \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>divrem_i32 a b \<equiv> FunctionBody \<lbrakk> (a / b, a % b) \<rbrakk>\<close>

definition divrem_i32_contract where
  \<open>divrem_i32_contract a b \<equiv>
    let pre  = \<langle>b \<noteq> 0 \<and> (sint a = - (2 ^ 31) \<longrightarrow> b \<noteq> -1)\<rangle> in
    let post = \<lambda>r. \<langle>fst r = a sdiv b \<and> fst (snd r) = a smod b\<rangle> in
    make_function_contract pre post\<close>

lemma divrem_i32_spec:
  shows \<open>\<Gamma>; divrem_i32 a b \<Turnstile>\<^sub>F divrem_i32_contract a b\<close>
  by (crush_boot f: divrem_i32_def contract: divrem_i32_contract_def) crush_base

definition divrem_u32 :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, 32 word \<times> 32 word \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>divrem_u32 a b \<equiv> FunctionBody \<lbrakk> (a / b, a % b) \<rbrakk>\<close>

definition divrem_u32_contract where
  \<open>divrem_u32_contract a b \<equiv>
    let pre  = \<langle>b \<noteq> 0\<rangle> in
    let post = \<lambda>r. \<langle>fst r = a div b \<and> fst (snd r) = a mod b\<rangle> in
    make_function_contract pre post\<close>

lemma divrem_u32_spec:
  shows \<open>\<Gamma>; divrem_u32 a b \<Turnstile>\<^sub>F divrem_u32_contract a b\<close>
  by (crush_boot f: divrem_u32_def contract: divrem_u32_contract_def) crush_base

text\<open>Division by a positive constant: the \<open>MIN / -1\<close> case is excluded by the constant.\<close>

definition halve_i32 :: \<open>32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>halve_i32 a \<equiv> FunctionBody \<lbrakk> a / 2_i32 \<rbrakk>\<close>

definition halve_i32_contract where
  \<open>halve_i32_contract a \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = a sdiv 2\<rangle> in
    make_function_contract pre post\<close>

lemma halve_i32_spec:
  shows \<open>\<Gamma>; halve_i32 a \<Turnstile>\<^sub>F halve_i32_contract a\<close>
  by (crush_boot f: halve_i32_def contract: halve_i32_contract_def) crush_base

definition halve_u32 :: \<open>32 word \<Rightarrow> ('s, 32 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>halve_u32 a \<equiv> FunctionBody \<lbrakk> a / 2_u32 \<rbrakk>\<close>

definition halve_u32_contract where
  \<open>halve_u32_contract a \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = a div 2\<rangle> in
    make_function_contract pre post\<close>

lemma halve_u32_spec:
  shows \<open>\<Gamma>; halve_u32 a \<Turnstile>\<^sub>F halve_u32_contract a\<close>
  by (crush_boot f: halve_u32_def contract: halve_u32_contract_def) crush_base

text\<open>Arithmetic right shift.\<close>

definition shr_i32 :: \<open>32 sword \<Rightarrow> 64 word \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>shr_i32 a s \<equiv> FunctionBody \<lbrakk> a >> s \<rbrakk>\<close>

definition shr_i32_contract where
  \<open>shr_i32_contract a s \<equiv>
    let pre  = \<langle>unat s < 32\<rangle> in
    let post = \<lambda>r. \<langle>r = signed_drop_bit (unat s) a\<rangle> in
    make_function_contract pre post\<close>

lemma shr_i32_spec:
  shows \<open>\<Gamma>; shr_i32 a s \<Turnstile>\<^sub>F shr_i32_contract a s\<close>
  by (crush_boot f: shr_i32_def contract: shr_i32_contract_def) crush_base

definition shr_u32 :: \<open>32 word \<Rightarrow> 64 word \<Rightarrow> ('s, 32 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>shr_u32 a s \<equiv> FunctionBody \<lbrakk> a >> s \<rbrakk>\<close>

definition shr_u32_contract where
  \<open>shr_u32_contract a s \<equiv>
    let pre  = \<langle>unat s < 32\<rangle> in
    let post = \<lambda>r. \<langle>r = drop_bit (unat s) a\<rangle> in
    make_function_contract pre post\<close>

lemma shr_u32_spec:
  shows \<open>\<Gamma>; shr_u32 a s \<Turnstile>\<^sub>F shr_u32_contract a s\<close>
  by (crush_boot f: shr_u32_def contract: shr_u32_contract_def) crush_base

definition shr1_i8 :: \<open>8 sword \<Rightarrow> ('s, 8 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>shr1_i8 a \<equiv> FunctionBody \<lbrakk> a >> 1_u64 \<rbrakk>\<close>

definition shr1_i8_contract where
  \<open>shr1_i8_contract a \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>sint r = sint a div 2\<rangle> in
    make_function_contract pre post\<close>

lemma shr1_i8_spec:
  shows \<open>\<Gamma>; shr1_i8 a \<Turnstile>\<^sub>F shr1_i8_contract a\<close>
  by (crush_boot f: shr1_i8_def contract: shr1_i8_contract_def)
    (crush_base simp add: sint_signed_drop_bit_eq drop_bit_eq_div)

text\<open>Unary minus.\<close>

definition neg_i8 :: \<open>8 sword \<Rightarrow> ('s, 8 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>neg_i8 a \<equiv> FunctionBody \<lbrakk> -a \<rbrakk>\<close>

definition neg_i8_contract where
  \<open>neg_i8_contract a \<equiv>
    let pre  = \<langle>sint a \<noteq> - 128\<rangle> in
    let post = \<lambda>r. \<langle>r = - a \<and> sint r = - sint a\<rangle> in
    make_function_contract pre post\<close>

text\<open>Crush has no rule for \<^const>\<open>word_uminus\<close> (it is neither a \<^verbatim>\<open>micro_rust_wp_intros\<close> rule
nor unfolded by \<^verbatim>\<open>micro_rust_simps\<close>), so \<^verbatim>\<open>word_uminus_def\<close> must be given; without it
\<^verbatim>\<open>crush_base\<close> stops at \<open>WP \<Gamma> (-\<^sub>\<mu> ascribei8 a) \<dots>\<close>. The bounds of \<^term>\<open>sint a\<close> are not
known to Crush either (as \<^verbatim>\<open>unat_lt2p\<close> for unsigned words).\<close>

lemma neg_i8_spec:
  shows \<open>\<Gamma>; neg_i8 a \<Turnstile>\<^sub>F neg_i8_contract a\<close>
  apply (crush_boot f: neg_i8_def contract: neg_i8_contract_def)
  using sint_range'[of a]
  apply (crush_base simp add: word_uminus_def sint_word_ariths signed_take_bit_int_eq_self)
  done

text\<open>Regression: unary minus needs no unfolding hint.\<close>

lemma neg_i8_spec_unhinted:
  shows \<open>\<Gamma>; neg_i8 a \<Turnstile>\<^sub>F neg_i8_contract a\<close>
  apply (crush_boot f: neg_i8_def contract: neg_i8_contract_def)
  using sint_range'[of a]
  apply (crush_base simp add: sint_word_ariths signed_take_bit_int_eq_self)
  done

text\<open>Subtracting from zero is the same operation written out.\<close>

definition neg_i8' :: \<open>8 sword \<Rightarrow> ('s, 8 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>neg_i8' a \<equiv> FunctionBody \<lbrakk> 0_i8 - a \<rbrakk>\<close>

lemma neg_i8'_spec:
  shows \<open>\<Gamma>; neg_i8' a \<Turnstile>\<^sub>F neg_i8_contract a\<close>
  apply (crush_boot f: neg_i8'_def contract: neg_i8_contract_def)
  using sint_range'[of a]
  apply (crush_base simp add: sint_word_ariths signed_take_bit_int_eq_self)
  done

subsection\<open>Crush end-to-end: comparisons, if/else, match\<close>

definition sign_i32 :: \<open>32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>sign_i32 x \<equiv> FunctionBody \<lbrakk>
    if x < 0_i32 {
      -1_i32
    } else if x > 0_i32 {
      1_i32
    } else {
      0_i32
    }
  \<rbrakk>\<close>

definition sign_i32_contract where
  \<open>sign_i32_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>sint r = sgn (sint x)\<rangle> in
    make_function_contract pre post\<close>

lemma sign_i32_spec:
  shows \<open>\<Gamma>; sign_i32 x \<Turnstile>\<^sub>F sign_i32_contract x\<close>
  by (crush_boot f: sign_i32_def contract: sign_i32_contract_def)
    (crush_base simp add: word_sless_alt)

definition clamp_i16 :: \<open>16 sword \<Rightarrow> 16 sword \<Rightarrow> 16 sword \<Rightarrow> ('s, 16 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>clamp_i16 lo hi x \<equiv> FunctionBody \<lbrakk>
    if x < lo { lo } else if x > hi { hi } else { x }
  \<rbrakk>\<close>

definition clamp_i16_contract where
  \<open>clamp_i16_contract lo hi x \<equiv>
    let pre  = \<langle>lo \<le>s hi\<rangle> in
    let post = \<lambda>r. \<langle>lo \<le>s r \<and> r \<le>s hi \<and> sint r = max (sint lo) (min (sint hi) (sint x))\<rangle> in
    make_function_contract pre post\<close>

lemma clamp_i16_spec:
  shows \<open>\<Gamma>; clamp_i16 lo hi x \<Turnstile>\<^sub>F clamp_i16_contract lo hi x\<close>
  by (crush_boot f: clamp_i16_def contract: clamp_i16_contract_def)
    (crush_base simp add: word_sle_eq word_sless_alt)

definition clamp_u16 :: \<open>16 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> ('s, 16 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>clamp_u16 lo hi x \<equiv> FunctionBody \<lbrakk>
    if x < lo { lo } else if x > hi { hi } else { x }
  \<rbrakk>\<close>

definition clamp_u16_contract where
  \<open>clamp_u16_contract lo hi x \<equiv>
    let pre  = \<langle>lo \<le> hi\<rangle> in
    let post = \<lambda>r. \<langle>lo \<le> r \<and> r \<le> hi \<and> unat r = max (unat lo) (min (unat hi) (unat x))\<rangle> in
    make_function_contract pre post\<close>

lemma clamp_u16_spec:
  shows \<open>\<Gamma>; clamp_u16 lo hi x \<Turnstile>\<^sub>F clamp_u16_contract lo hi x\<close>
  by (crush_boot f: clamp_u16_def contract: clamp_u16_contract_def)
    (crush_base simp add: word_le_nat_alt word_less_nat_alt)

text\<open>Comparisons with negative literals: the signed order must be used.\<close>

definition is_small_negative :: \<open>32 sword \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>is_small_negative x \<equiv> FunctionBody \<lbrakk> x >= -10_i32 && x < 0_i32 \<rbrakk>\<close>

definition is_small_negative_contract where
  \<open>is_small_negative_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r \<longleftrightarrow> -10 \<le> sint x \<and> sint x < 0\<rangle> in
    make_function_contract pre post\<close>

lemma is_small_negative_spec:
  shows \<open>\<Gamma>; is_small_negative x \<Turnstile>\<^sub>F is_small_negative_contract x\<close>
  by (crush_boot f: is_small_negative_def contract: is_small_negative_contract_def)
    (crush_base simp add: word_sle_eq word_sless_alt)

subsection\<open>Crush end-to-end: casts\<close>

text\<open>Widening signed to signed preserves the value; widening unsigned to signed too.\<close>

definition widen_i8_i32 :: \<open>8 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>widen_i8_i32 x \<equiv> FunctionBody \<lbrakk> x as i32 \<rbrakk>\<close>

definition widen_i8_i32_contract where
  \<open>widen_i8_i32_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = scast x \<and> sint r = sint x\<rangle> in
    make_function_contract pre post\<close>

lemma widen_i8_i32_spec:
  shows \<open>\<Gamma>; widen_i8_i32 x \<Turnstile>\<^sub>F widen_i8_i32_contract x\<close>
  by (crush_boot f: widen_i8_i32_def contract: widen_i8_i32_contract_def)
    (crush_base simp add: sint_up_scast is_up)

definition widen_u8_u32 :: \<open>8 word \<Rightarrow> ('s, 32 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>widen_u8_u32 x \<equiv> FunctionBody \<lbrakk> x as u32 \<rbrakk>\<close>

definition widen_u8_u32_contract where
  \<open>widen_u8_u32_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = ucast x \<and> unat r = unat x\<rangle> in
    make_function_contract pre post\<close>

lemma widen_u8_u32_spec:
  shows \<open>\<Gamma>; widen_u8_u32 x \<Turnstile>\<^sub>F widen_u8_u32_contract x\<close>
  by (crush_boot f: widen_u8_u32_def contract: widen_u8_u32_contract_def)
    (crush_base simp add: unat_ucast_upcast is_up)

definition widen_u8_i32 :: \<open>8 word \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>widen_u8_i32 x \<equiv> FunctionBody \<lbrakk> x as i32 \<rbrakk>\<close>

definition widen_u8_i32_contract where
  \<open>widen_u8_i32_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = ucast x \<and> sint r = uint x \<and> 0 \<le> sint r\<rangle> in
    make_function_contract pre post\<close>

lemma widen_u8_i32_spec:
  shows \<open>\<Gamma>; widen_u8_i32 x \<Turnstile>\<^sub>F widen_u8_i32_contract x\<close>
  by (crush_boot f: widen_u8_i32_def contract: widen_u8_i32_contract_def)
    (crush_base simp add: sint_ucast_eq_uint is_down)

text\<open>Signed to unsigned of the same width: the bit pattern is kept.\<close>

definition i32_as_u32 :: \<open>32 sword \<Rightarrow> ('s, 32 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>i32_as_u32 x \<equiv> FunctionBody \<lbrakk> x as u32 \<rbrakk>\<close>

definition i32_as_u32_contract where
  \<open>i32_as_u32_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = scast x \<and> (x = -1 \<longrightarrow> r = 4294967295) \<and> (x = 5 \<longrightarrow> r = 5)\<rangle> in
    make_function_contract pre post\<close>

lemma i32_as_u32_spec:
  shows \<open>\<Gamma>; i32_as_u32 x \<Turnstile>\<^sub>F i32_as_u32_contract x\<close>
  by (crush_boot f: i32_as_u32_def contract: i32_as_u32_contract_def) crush_base

definition u32_as_i32 :: \<open>32 word \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>u32_as_i32 x \<equiv> FunctionBody \<lbrakk> x as i32 \<rbrakk>\<close>

definition u32_as_i32_contract where
  \<open>u32_as_i32_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = ucast x \<and> (x = 4294967295 \<longrightarrow> sint r = -1) \<and> (x = 5 \<longrightarrow> sint r = 5)\<rangle> in
    make_function_contract pre post\<close>

lemma u32_as_i32_spec:
  shows \<open>\<Gamma>; u32_as_i32 x \<Turnstile>\<^sub>F u32_as_i32_contract x\<close>
  by (crush_boot f: u32_as_i32_def contract: u32_as_i32_contract_def) crush_base

text\<open>Narrowing: signed to signed truncates and reinterprets; signed to unsigned truncates.\<close>

definition narrow_i32_i8 :: \<open>32 sword \<Rightarrow> ('s, 8 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>narrow_i32_i8 x \<equiv> FunctionBody \<lbrakk> x as i8 \<rbrakk>\<close>

definition narrow_i32_i8_contract where
  \<open>narrow_i32_i8_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = scast x \<and> (- 128 \<le> sint x \<and> sint x < 128 \<longrightarrow> sint r = sint x)\<rangle> in
    make_function_contract pre post\<close>

lemma narrow_i32_i8_spec:
  shows \<open>\<Gamma>; narrow_i32_i8 x \<Turnstile>\<^sub>F narrow_i32_i8_contract x\<close>
  by (crush_boot f: narrow_i32_i8_def contract: narrow_i32_i8_contract_def)
    (crush_base simp add: signed_scast_eq signed_take_bit_int_eq_self)

definition narrow_i32_u8 :: \<open>32 sword \<Rightarrow> ('s, 8 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>narrow_i32_u8 x \<equiv> FunctionBody \<lbrakk> x as u8 \<rbrakk>\<close>

definition narrow_i32_u8_contract where
  \<open>narrow_i32_u8_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = scast x \<and> (x = -1 \<longrightarrow> r = 255) \<and> (x = 300 \<longrightarrow> r = 44)\<rangle> in
    make_function_contract pre post\<close>

lemma narrow_i32_u8_spec:
  shows \<open>\<Gamma>; narrow_i32_u8 x \<Turnstile>\<^sub>F narrow_i32_u8_contract x\<close>
  by (crush_boot f: narrow_i32_u8_def contract: narrow_i32_u8_contract_def) crush_base

definition narrow_u32_u8 :: \<open>32 word \<Rightarrow> ('s, 8 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>narrow_u32_u8 x \<equiv> FunctionBody \<lbrakk> x as u8 \<rbrakk>\<close>

definition narrow_u32_u8_contract where
  \<open>narrow_u32_u8_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = ucast x \<and> (unat x < 256 \<longrightarrow> unat r = unat x)\<rangle> in
    make_function_contract pre post\<close>

lemma narrow_u32_u8_spec:
  shows \<open>\<Gamma>; narrow_u32_u8 x \<Turnstile>\<^sub>F narrow_u32_u8_contract x\<close>
  by (crush_boot f: narrow_u32_u8_def contract: narrow_u32_u8_contract_def)
    (crush_base simp add: unat_ucast)

definition narrow_u32_i8 :: \<open>32 word \<Rightarrow> ('s, 8 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>narrow_u32_i8 x \<equiv> FunctionBody \<lbrakk> x as i8 \<rbrakk>\<close>

definition narrow_u32_i8_contract where
  \<open>narrow_u32_i8_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = ucast x \<and> (x = 255 \<longrightarrow> sint r = -1)\<rangle> in
    make_function_contract pre post\<close>

lemma narrow_u32_i8_spec:
  shows \<open>\<Gamma>; narrow_u32_i8 x \<Turnstile>\<^sub>F narrow_u32_i8_contract x\<close>
  by (crush_boot f: narrow_u32_i8_def contract: narrow_u32_i8_contract_def) crush_base

text\<open>\<open>isize\<close>/\<open>usize\<close> and 64-bit casts.\<close>

definition cast_isize :: \<open>32 sword \<Rightarrow> 64 word \<Rightarrow> ('s, 64 sword \<times> 64 word \<times> 64 sword \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>cast_isize x y \<equiv> FunctionBody \<lbrakk> (x as isize, x as usize, y as isize) \<rbrakk>\<close>

definition cast_isize_contract where
  \<open>cast_isize_contract x y \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>sint (fst r) = sint x \<and> fst (snd r) = scast x \<and> fst (snd (snd r)) = ucast y\<rangle> in
    make_function_contract pre post\<close>

lemma cast_isize_spec:
  shows \<open>\<Gamma>; cast_isize x y \<Turnstile>\<^sub>F cast_isize_contract x y\<close>
  by (crush_boot f: cast_isize_def contract: cast_isize_contract_def)
    (crush_base simp add: sint_up_scast is_up)

text\<open>A cast followed by arithmetic: widening before adding avoids the overflow check.\<close>

definition add_widened :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, 64 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>add_widened a b \<equiv> FunctionBody \<lbrakk> (a as i64) + (b as i64) \<rbrakk>\<close>

definition add_widened_contract where
  \<open>add_widened_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>sint r = sint a + sint b\<rangle> in
    make_function_contract pre post\<close>

lemma add_widened_spec:
  shows \<open>\<Gamma>; add_widened a b \<Turnstile>\<^sub>F add_widened_contract a b\<close>
  apply (crush_boot f: add_widened_def contract: add_widened_contract_def)
  using sint_range'[of a] sint_range'[of b]
  apply (crush_base simp add: sint_up_scast is_up sint_word_ariths signed_take_bit_int_eq_self)
  done

definition add_widened_u :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, 64 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>add_widened_u a b \<equiv> FunctionBody \<lbrakk> (a as u64) + (b as u64) \<rbrakk>\<close>

definition add_widened_u_contract where
  \<open>add_widened_u_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>unat r = unat a + unat b\<rangle> in
    make_function_contract pre post\<close>

lemma add_widened_u_spec:
  shows \<open>\<Gamma>; add_widened_u a b \<Turnstile>\<^sub>F add_widened_u_contract a b\<close>
  apply (crush_boot f: add_widened_u_def contract: add_widened_u_contract_def)
  using unat_lt2p[of a] unat_lt2p[of b]
  apply (crush_base simp add: unat_ucast_upcast is_up unat_add_lem')
  done

subsection\<open>Crush end-to-end: modular verification\<close>

definition add3_i8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> 8 sword \<Rightarrow> ('s, 8 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>add3_i8 a b c \<equiv> FunctionBody \<lbrakk> add_i8(add_i8(a, b), c) \<rbrakk>\<close>

definition add3_i8_contract where
  \<open>add3_i8_contract a b c \<equiv>
    let pre  = \<langle>- 128 \<le> sint a + sint b \<and> sint a + sint b < 128 \<and>
                - 128 \<le> sint a + sint b + sint c \<and> sint a + sint b + sint c < 128\<rangle> in
    let post = \<lambda>r. \<langle>sint r = sint a + sint b + sint c\<rangle> in
    make_function_contract pre post\<close>

lemma add3_i8_spec:
  shows \<open>\<Gamma>; add3_i8 a b c \<Turnstile>\<^sub>F add3_i8_contract a b c\<close>
  by (crush_boot f: add3_i8_def contract: add3_i8_contract_def)
    (crush_base specs add: add_i8_spec contracts add: add_i8_contract_def)

definition add3_u8 :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> ('s, 8 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>add3_u8 a b c \<equiv> FunctionBody \<lbrakk> add_u8(add_u8(a, b), c) \<rbrakk>\<close>

definition add3_u8_contract where
  \<open>add3_u8_contract a b c \<equiv>
    let pre  = \<langle>unat a + unat b + unat c < 256\<rangle> in
    let post = \<lambda>r. \<langle>unat r = unat a + unat b + unat c\<rangle> in
    make_function_contract pre post\<close>

lemma add3_u8_spec:
  shows \<open>\<Gamma>; add3_u8 a b c \<Turnstile>\<^sub>F add3_u8_contract a b c\<close>
  by (crush_boot f: add3_u8_def contract: add3_u8_contract_def)
    (crush_base specs add: add_u8_spec contracts add: add_u8_contract_def)

subsection\<open>Crush end-to-end: standard library calls on signed values\<close>

definition sat_sub_i8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> ('s, 8 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>sat_sub_i8 a b \<equiv> FunctionBody \<lbrakk> a.saturating_sub(b) \<rbrakk>\<close>

definition sat_sub_i8_contract where
  \<open>sat_sub_i8_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>sint r = max (-128) (min 127 (sint a - sint b))\<rangle> in
    make_function_contract pre post\<close>

lemma sat_sub_i8_spec:
  shows \<open>\<Gamma>; sat_sub_i8 a b \<Turnstile>\<^sub>F sat_sub_i8_contract a b\<close>
  by (crush_boot f: sat_sub_i8_def contract: sat_sub_i8_contract_def)
    (crush_base simp add: sint_word_ariths signed_take_bit_int_eq_self)

definition sat_sub_u8 :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> ('s, 8 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>sat_sub_u8 a b \<equiv> FunctionBody \<lbrakk> a.saturating_sub(b) \<rbrakk>\<close>

definition sat_sub_u8_contract where
  \<open>sat_sub_u8_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>unat r = unat a - unat b\<rangle> in
    make_function_contract pre post\<close>

lemma sat_sub_u8_spec:
  shows \<open>\<Gamma>; sat_sub_u8 a b \<Turnstile>\<^sub>F sat_sub_u8_contract a b\<close>
  by (crush_boot f: sat_sub_u8_def contract: sat_sub_u8_contract_def)
    (crush_base simp add: unat_sub_if_size word_size word_less_nat_alt)

definition ovf_mul_i8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> ('s, 8 sword \<times> bool \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>ovf_mul_i8 a b \<equiv> FunctionBody \<lbrakk> a.overflowing_mul(b) \<rbrakk>\<close>

definition ovf_mul_i8_contract where
  \<open>ovf_mul_i8_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>fst r = a * b \<and> (fst (snd r) \<longleftrightarrow> sint a * sint b < -128 \<or> 128 \<le> sint a * sint b)\<rangle> in
    make_function_contract pre post\<close>

lemma ovf_mul_i8_spec:
  shows \<open>\<Gamma>; ovf_mul_i8 a b \<Turnstile>\<^sub>F ovf_mul_i8_contract a b\<close>
  by (crush_boot f: ovf_mul_i8_def contract: ovf_mul_i8_contract_def) crush_base

definition div_ceil_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>div_ceil_i32 a b \<equiv> FunctionBody \<lbrakk> a.div_ceil(b) \<rbrakk>\<close>

definition div_ceil_i32_contract where
  \<open>div_ceil_i32_contract a b \<equiv>
    let pre  = \<langle>b \<noteq> 0 \<and> (sint a = - (2 ^ 31) \<longrightarrow> b \<noteq> -1)\<rangle> in
    let post = \<lambda>r. \<langle>r = word_of_int (- ((- sint a) div sint b))\<rangle> in
    make_function_contract pre post\<close>

lemma div_ceil_i32_spec:
  shows \<open>\<Gamma>; div_ceil_i32 a b \<Turnstile>\<^sub>F div_ceil_i32_contract a b\<close>
  by (crush_boot f: div_ceil_i32_def contract: div_ceil_i32_contract_def) crush_base

definition div_ceil_u32 :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, 32 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>div_ceil_u32 a b \<equiv> FunctionBody \<lbrakk> a.div_ceil(b) \<rbrakk>\<close>

definition div_ceil_u32_contract where
  \<open>div_ceil_u32_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = (a + b - 1) div b\<rangle> in
    make_function_contract pre post\<close>

lemma div_ceil_u32_spec:
  shows \<open>\<Gamma>; div_ceil_u32 a b \<Turnstile>\<^sub>F div_ceil_u32_contract a b\<close>
  by (crush_boot f: div_ceil_u32_def contract: div_ceil_u32_contract_def) crush_base

text\<open>The signed \<open>div_ceil\<close> rounds towards positive infinity (concrete instances of the contract).\<close>

lemma div_ceil_signed_values:
  shows \<open>(word_of_int (- ((- sint (7 :: 32 sword)) div sint (2 :: 32 sword))) :: 32 sword) = 4\<close>
    and \<open>(word_of_int (- ((- sint (-7 :: 32 sword)) div sint (2 :: 32 sword))) :: 32 sword) = -3\<close>
    and \<open>(word_of_int (- ((- sint (7 :: 32 sword)) div sint (-2 :: 32 sword))) :: 32 sword) = -3\<close>
  by simp_all

definition wrap_add_unsigned_i32 :: \<open>32 sword \<Rightarrow> 32 word \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>wrap_add_unsigned_i32 a b \<equiv> FunctionBody \<lbrakk> a.wrapping_add_unsigned(b) \<rbrakk>\<close>

definition wrap_add_unsigned_i32_contract where
  \<open>wrap_add_unsigned_i32_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = a + ucast b\<rangle> in
    make_function_contract pre post\<close>

lemma wrap_add_unsigned_i32_spec:
  shows \<open>\<Gamma>; wrap_add_unsigned_i32 a b \<Turnstile>\<^sub>F wrap_add_unsigned_i32_contract a b\<close>
  by (crush_boot f: wrap_add_unsigned_i32_def contract: wrap_add_unsigned_i32_contract_def) crush_base

text\<open>\<open>checked_add\<close> has no contract in the standard library; it is unfolded.\<close>

definition checked_add_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, 32 sword option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>checked_add_i32 a b \<equiv> FunctionBody \<lbrakk> a.checked_add(b) \<rbrakk>\<close>

definition checked_add_i32_contract where
  \<open>checked_add_i32_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = (if - (2 ^ 31) \<le> sint a + sint b \<and> sint a + sint b < 2 ^ 31 then Some (a + b) else None)\<rangle> in
    make_function_contract pre post\<close>

lemma checked_add_i32_spec:
  shows \<open>\<Gamma>; checked_add_i32 a b \<Turnstile>\<^sub>F checked_add_i32_contract a b\<close>
  by (crush_boot f: checked_add_i32_def contract: checked_add_i32_contract_def)
    (crush_base simp add: checked_add_def checked_add_core_def)

definition checked_add_u32 :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, 32 word option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>checked_add_u32 a b \<equiv> FunctionBody \<lbrakk> a.checked_add(b) \<rbrakk>\<close>

definition checked_add_u32_contract where
  \<open>checked_add_u32_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = (if unat a + unat b < 2 ^ 32 then Some (a + b) else None)\<rangle> in
    make_function_contract pre post\<close>

lemma checked_add_u32_spec:
  shows \<open>\<Gamma>; checked_add_u32 a b \<Turnstile>\<^sub>F checked_add_u32_contract a b\<close>
  by (crush_boot f: checked_add_u32_def contract: checked_add_u32_contract_def)
    (crush_base simp add: checked_add_def checked_add_core_def)

text\<open>Ranges of signed values.\<close>

definition range_test_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, bool \<times> bool \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>range_test_i32 lo hi x \<equiv> FunctionBody \<lbrakk>
    let r = lo..hi;
    (r.is_empty(), r.contains(x))
  \<rbrakk>\<close>

definition range_test_i32_contract where
  \<open>range_test_i32_contract lo hi x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>(fst r \<longleftrightarrow> sint hi \<le> sint lo) \<and> (fst (snd r) \<longleftrightarrow> sint lo \<le> sint x \<and> sint x < sint hi)\<rangle> in
    make_function_contract pre post\<close>

lemma range_test_i32_spec:
  shows \<open>\<Gamma>; range_test_i32 lo hi x \<Turnstile>\<^sub>F range_test_i32_contract lo hi x\<close>
  by (crush_boot f: range_test_i32_def contract: range_test_i32_contract_def)
    (crush_base simp add: word_sle_eq word_sless_alt not_less)

definition range_test_u32 :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> ('s, bool \<times> bool \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>range_test_u32 lo hi x \<equiv> FunctionBody \<lbrakk>
    let r = lo..hi;
    (r.is_empty(), r.contains(x))
  \<rbrakk>\<close>

definition range_test_u32_contract where
  \<open>range_test_u32_contract lo hi x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>(fst r \<longleftrightarrow> unat hi \<le> unat lo) \<and> (fst (snd r) \<longleftrightarrow> unat lo \<le> unat x \<and> unat x < unat hi)\<rangle> in
    make_function_contract pre post\<close>

lemma range_test_u32_spec:
  shows \<open>\<Gamma>; range_test_u32 lo hi x \<Turnstile>\<^sub>F range_test_u32_contract lo hi x\<close>
  by (crush_boot f: range_test_u32_def contract: range_test_u32_contract_def)
    (crush_base simp add: word_le_nat_alt word_less_nat_alt not_less)

subsection\<open>Crush end-to-end: generic in the length\<close>

definition add_gen :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>add_gen a b \<equiv> FunctionBody \<lbrakk> a + b \<rbrakk>\<close>

definition add_gen_contract_signed :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s::sepalg, 'l word, 'abort) function_contract\<close> where
  \<open>add_gen_contract_signed a b \<equiv>
    let pre  = \<langle>- (2 ^ (LENGTH('l) - 1)) \<le> sint a + sint b \<and> sint a + sint b < 2 ^ (LENGTH('l) - 1)\<rangle> in
    let post = \<lambda>r. \<langle>r = a + b\<rangle> in
    make_function_contract pre post\<close>

definition add_gen_contract_unsigned :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s::sepalg, 'l word, 'abort) function_contract\<close> where
  \<open>add_gen_contract_unsigned a b \<equiv>
    let pre  = \<langle>unat a + unat b < 2 ^ LENGTH('l)\<rangle> in
    let post = \<lambda>r. \<langle>r = a + b\<rangle> in
    make_function_contract pre post\<close>

definition add_gen_contract_both :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s::sepalg, 'l word, 'abort) function_contract\<close> where
  \<open>add_gen_contract_both a b \<equiv>
    let pre  = \<langle>if is_signed TYPE('l) then - (2 ^ (LENGTH('l) - 1)) \<le> sint a + sint b \<and> sint a + sint b < 2 ^ (LENGTH('l) - 1)
                else unat a + unat b < 2 ^ LENGTH('l)\<rangle> in
    let post = \<lambda>r. \<langle>r = a + b\<rangle> in
    make_function_contract pre post\<close>

lemma add_gen_spec_signed:
  fixes a b :: \<open>'l::len word\<close>
  assumes \<open>is_signed TYPE('l)\<close>
  shows \<open>\<Gamma>; add_gen a b \<Turnstile>\<^sub>F add_gen_contract_signed a b\<close>
  using assms by (crush_boot f: add_gen_def contract: add_gen_contract_signed_def) crush_base

lemma add_gen_spec_unsigned:
  fixes a b :: \<open>'l::len word\<close>
  assumes \<open>\<not> is_signed TYPE('l)\<close>
  shows \<open>\<Gamma>; add_gen a b \<Turnstile>\<^sub>F add_gen_contract_unsigned a b\<close>
  using assms by (crush_boot f: add_gen_def contract: add_gen_contract_unsigned_def) crush_base

lemma add_gen_spec_both:
  fixes a b :: \<open>'l::len word\<close>
  shows \<open>\<Gamma>; add_gen a b \<Turnstile>\<^sub>F add_gen_contract_both a b\<close>
  by (crush_boot f: add_gen_def contract: add_gen_contract_both_def) crush_base

text\<open>The generic specifications instantiate to the concrete ones.\<close>

lemma add_gen_spec_i32:
  fixes a b :: \<open>32 sword\<close>
  shows \<open>\<Gamma>; add_gen a b \<Turnstile>\<^sub>F add_gen_contract_signed a b\<close>
  by (rule add_gen_spec_signed) simp

lemma add_gen_spec_u32:
  fixes a b :: \<open>32 word\<close>
  shows \<open>\<Gamma>; add_gen a b \<Turnstile>\<^sub>F add_gen_contract_unsigned a b\<close>
  by (rule add_gen_spec_unsigned) simp

lemma add_gen_contract_both_i32:
  fixes a b :: \<open>32 sword\<close>
  shows \<open>add_gen_contract_both a b = add_gen_contract_signed a b\<close>
  by (simp add: add_gen_contract_both_def add_gen_contract_signed_def)

definition cmp_gen :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>cmp_gen a b \<equiv> FunctionBody \<lbrakk> a < b \<rbrakk>\<close>

definition cmp_gen_contract :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s::sepalg, bool, 'abort) function_contract\<close> where
  \<open>cmp_gen_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r \<longleftrightarrow> word_rust_lt a b\<rangle> in
    make_function_contract pre post\<close>

text\<open>Regression: a comparison at a length that is generic in its signedness is evaluated by Crush.\<close>

lemma cmp_gen_spec:
  fixes a b :: \<open>'l::len word\<close>
  shows \<open>\<Gamma>; cmp_gen a b \<Turnstile>\<^sub>F cmp_gen_contract a b\<close>
  by (crush_boot f: cmp_gen_def contract: cmp_gen_contract_def) crush_base

lemma cmp_gen_spec_hinted:
  fixes a b :: \<open>'l::len word\<close>
  shows \<open>\<Gamma>; cmp_gen a b \<Turnstile>\<^sub>F cmp_gen_contract a b\<close>
  by (crush_boot f: cmp_gen_def contract: cmp_gen_contract_def) (crush_base simp add: comp_lt_def)

definition cmp_gen_contract_signed :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s::sepalg, bool, 'abort) function_contract\<close> where
  \<open>cmp_gen_contract_signed a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r \<longleftrightarrow> a <s b\<rangle> in
    make_function_contract pre post\<close>

lemma cmp_gen_spec_signed:
  fixes a b :: \<open>'l::len word\<close>
  assumes \<open>is_signed TYPE('l)\<close>
  shows \<open>\<Gamma>; cmp_gen a b \<Turnstile>\<^sub>F cmp_gen_contract_signed a b\<close>
  using assms by (crush_boot f: cmp_gen_def contract: cmp_gen_contract_signed_def) crush_base

subsection\<open>Crush end-to-end: mutable locals and loops\<close>

locale signed_test_ctx =
    reference reference_types +
    ref_i32: reference_allocatable reference_types _ _ _ _ _ _ _ i32_prism +
    ref_u32: reference_allocatable reference_types _ _ _ _ _ _ _ u32_prism +
    ref_i64: reference_allocatable reference_types _ _ _ _ _ _ _ i64_prism +
    ref_u64: reference_allocatable reference_types _ _ _ _ _ _ _ u64_prism +
    ref_nat: reference_allocatable reference_types _ _ _ _ _ _ _ nat_prism
  for
  reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and i32_prism :: \<open>('gv, 32 sword) prism\<close>
  and u32_prism :: \<open>('gv, 32 word) prism\<close>
  and i64_prism :: \<open>('gv, 64 sword) prism\<close>
  and u64_prism :: \<open>('gv, 64 word) prism\<close>
  and nat_prism :: \<open>('gv, nat) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_i32.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_u32.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_i64.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_u64.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_nat.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

definition abs_i32 :: \<open>32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>abs_i32 x \<equiv> FunctionBody \<lbrakk>
    let mut r = x;
    if x < 0_i32 {
      r = 0_i32 - x;
    };
    *r
  \<rbrakk>\<close>

definition abs_i32_contract where
  \<open>abs_i32_contract x \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>sint x \<noteq> - (2 ^ 31)\<rangle> in
    let post = \<lambda>r. can_alloc_reference \<star> \<langle>sint r = \<bar>sint x\<bar>\<rangle> in
    make_function_contract pre post\<close>

lemma abs_i32_spec:
  shows \<open>\<Gamma>; abs_i32 x \<Turnstile>\<^sub>F abs_i32_contract x\<close>
  apply (crush_boot f: abs_i32_def contract: abs_i32_contract_def)
  using sint_range'[of x]
  apply (crush_base simp add: word_sless_alt sint_word_ariths signed_take_bit_int_eq_self)
  done

definition abs_diff_u32 :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, 32 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>abs_diff_u32 a b \<equiv> FunctionBody \<lbrakk>
    let mut r = 0_u32;
    if a > b {
      r = a - b;
    } else {
      r = b - a;
    };
    *r
  \<rbrakk>\<close>

definition abs_diff_u32_contract where
  \<open>abs_diff_u32_contract a b \<equiv>
    let pre  = can_alloc_reference in
    let post = \<lambda>r. can_alloc_reference \<star> \<langle>unat r = max (unat a) (unat b) - min (unat a) (unat b)\<rangle> in
    make_function_contract pre post\<close>

lemma abs_diff_u32_spec:
  shows \<open>\<Gamma>; abs_diff_u32 a b \<Turnstile>\<^sub>F abs_diff_u32_contract a b\<close>
  by (crush_boot f: abs_diff_u32_def contract: abs_diff_u32_contract_def)
    (crush_base simp add: unat_sub_if_size word_size word_less_nat_alt word_le_nat_alt)

definition abs_diff_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>abs_diff_i32 a b \<equiv> FunctionBody \<lbrakk>
    let mut r = 0_i32;
    if a > b {
      r = a - b;
    } else {
      r = b - a;
    };
    *r
  \<rbrakk>\<close>

definition abs_diff_i32_contract where
  \<open>abs_diff_i32_contract a b \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>\<bar>sint a - sint b\<bar> < 2 ^ 31\<rangle> in
    let post = \<lambda>r. can_alloc_reference \<star> \<langle>sint r = \<bar>sint a - sint b\<bar>\<rangle> in
    make_function_contract pre post\<close>

lemma abs_diff_i32_spec:
  shows \<open>\<Gamma>; abs_diff_i32 a b \<Turnstile>\<^sub>F abs_diff_i32_contract a b\<close>
  by (crush_boot f: abs_diff_i32_def contract: abs_diff_i32_contract_def)
    (crush_base simp add: word_sless_alt sint_word_ariths signed_take_bit_int_eq_self)

text\<open>A counter accumulated across a signed range, with a loop invariant.\<close>

text\<open>The number of iterations of a loop over a signed range (as in \<^verbatim>\<open>Showcase.sum_spec\<close>, the
accumulator is a natural number).\<close>

adhoc_overloading urust_add \<rightleftharpoons> \<open>bind2 (lift_exp2 (plus :: nat \<Rightarrow> nat \<Rightarrow> nat))\<close>

definition count_range_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>count_range_i32 lo hi \<equiv> FunctionBody \<lbrakk>
    let mut cnt = \<llangle>0 :: nat\<rrangle>;
    for i in lo..hi {
      cnt = *cnt + \<llangle>1 :: nat\<rrangle>;
    };
    *cnt
  \<rbrakk>\<close>

definition count_range_i32_contract where
  \<open>count_range_i32_contract lo hi \<equiv>
    let pre  = can_alloc_reference in
    let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = nat (sint hi - sint lo)\<rangle> in
    make_function_contract pre post\<close>

lemma count_range_i32_spec:
  shows \<open>\<Gamma>; count_range_i32 lo hi \<Turnstile>\<^sub>F count_range_i32_contract lo hi\<close>
proof (crush_boot f: count_range_i32_def contract: count_range_i32_contract_def, goal_cases)
  case 1
  show ?case
    apply crush_base
    subgoal for cnt_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g. cnt_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'\<close>)
      by crush_base
    done
qed

definition count_range_u32 :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>count_range_u32 lo hi \<equiv> FunctionBody \<lbrakk>
    let mut cnt = \<llangle>0 :: nat\<rrangle>;
    for i in lo..hi {
      cnt = *cnt + \<llangle>1 :: nat\<rrangle>;
    };
    *cnt
  \<rbrakk>\<close>

definition count_range_u32_contract where
  \<open>count_range_u32_contract lo hi \<equiv>
    let pre  = can_alloc_reference in
    let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = unat hi - unat lo\<rangle> in
    make_function_contract pre post\<close>

lemma count_range_u32_spec:
  shows \<open>\<Gamma>; count_range_u32 lo hi \<Turnstile>\<^sub>F count_range_u32_contract lo hi\<close>
proof (crush_boot f: count_range_u32_def contract: count_range_u32_contract_def, goal_cases)
  case 1
  show ?case
    apply crush_base
    subgoal for cnt_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g. cnt_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>i\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'\<close>)
      by crush_base
    done
qed

text\<open>Comparing the loop variable with the bounds inside the body needs, for signed and unsigned
ranges alike, facts about \<open>sint (lo + word_of_nat i)\<close> resp. \<open>unat (lo + word_of_nat i)\<close> that
Crush does not derive on its own; such bodies are not tested here.\<close>

end

subsection\<open>Crush end-to-end: tests with syntax that may not parse\<close>

text\<open>These are placed last: a statement that fails to parse stops the checking of the theory.\<close>

text\<open>\<open>match\<close> on signed values with negative patterns and a guard.\<close>

definition classify_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>classify_i32 x y \<equiv> FunctionBody \<lbrakk>
    match x {
      -1 \<Rightarrow> 10_i32,
      0 \<Rightarrow> 20_i32,
      -128 \<Rightarrow> 30_i32,
      1 if y > 0_i32 \<Rightarrow> 40_i32,
      1 \<Rightarrow> 45_i32,
      _ \<Rightarrow> 50_i32
    }
  \<rbrakk>\<close>

definition classify_i32_contract where
  \<open>classify_i32_contract x y \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = (if x = -1 then 10 else if x = 0 then 20 else if x = -128 then 30
                          else if x = 1 then (if 0 < sint y then 40 else 45) else 50)\<rangle> in
    make_function_contract pre post\<close>

lemma classify_i32_spec:
  shows \<open>\<Gamma>; classify_i32 x y \<Turnstile>\<^sub>F classify_i32_contract x y\<close>
  by (crush_boot f: classify_i32_def contract: classify_i32_contract_def)
    (crush_base simp add: ncase_simps word_sless_alt)

definition classify_u32 :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, 32 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>classify_u32 x y \<equiv> FunctionBody \<lbrakk>
    match x {
      2 \<Rightarrow> 10_u32,
      0 \<Rightarrow> 20_u32,
      128 \<Rightarrow> 30_u32,
      1 if y > 200_u32 \<Rightarrow> 40_u32,
      1 \<Rightarrow> 45_u32,
      _ \<Rightarrow> 50_u32
    }
  \<rbrakk>\<close>

definition classify_u32_contract where
  \<open>classify_u32_contract x y \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = (if x = 2 then 10 else if x = 0 then 20 else if x = 128 then 30
                          else if x = 1 then (if 200 < unat y then 40 else 45) else 50)\<rangle> in
    make_function_contract pre post\<close>

lemma classify_u32_spec:
  shows \<open>\<Gamma>; classify_u32 x y \<Turnstile>\<^sub>F classify_u32_contract x y\<close>
  by (crush_boot f: classify_u32_def contract: classify_u32_contract_def)
    (crush_base simp add: ncase_simps word_less_nat_alt)

definition ovf_add_i32 :: \<open>32 sword \<Rightarrow> 32 sword \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>ovf_add_i32 a b \<equiv> FunctionBody \<lbrakk>
    let (r, ov) = a.overflowing_add(b);
    ov
  \<rbrakk>\<close>

definition ovf_add_i32_contract where
  \<open>ovf_add_i32_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r \<longleftrightarrow> sint a + sint b < - (2 ^ 31) \<or> 2 ^ 31 \<le> sint a + sint b\<rangle> in
    make_function_contract pre post\<close>

lemma ovf_add_i32_spec:
  shows \<open>\<Gamma>; ovf_add_i32 a b \<Turnstile>\<^sub>F ovf_add_i32_contract a b\<close>
  by (crush_boot f: ovf_add_i32_def contract: ovf_add_i32_contract_def) crush_base

text\<open>With the postcondition phrased as \<open>\<not> (- (2 ^ 31) \<le> sint a + sint b \<and> sint a + sint b < 2 ^ 31)\<close>
instead, \<^verbatim>\<open>crush_base\<close> leaves the propositional goal
\<open>(sint a + sint b < - 2^31 \<or> 2^31 \<le> sint a + sint b) = (- 2^31 \<le> sint a + sint b \<longrightarrow> \<not> sint a + sint b < 2^31)\<close>
open (it is closed by \<open>auto\<close>); the unsigned analogue is stated in the form of the contract.\<close>

definition ovf_add_u32 :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>ovf_add_u32 a b \<equiv> FunctionBody \<lbrakk>
    let (r, ov) = a.overflowing_add(b);
    ov
  \<rbrakk>\<close>

definition ovf_add_u32_contract where
  \<open>ovf_add_u32_contract a b \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r \<longleftrightarrow> 2 ^ 32 \<le> unat a + unat b\<rangle> in
    make_function_contract pre post\<close>

lemma ovf_add_u32_spec:
  shows \<open>\<Gamma>; ovf_add_u32 a b \<Turnstile>\<^sub>F ovf_add_u32_contract a b\<close>
  by (crush_boot f: ovf_add_u32_def contract: ovf_add_u32_contract_def) crush_base

definition nonzero_i64_test :: \<open>64 sword \<Rightarrow> ('s, nonzero_i64 option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>nonzero_i64_test x \<equiv> FunctionBody \<lbrakk> NonZeroI64::new(x) \<rbrakk>\<close>

definition nonzero_i64_test_contract where
  \<open>nonzero_i64_test_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r = nonzeroi64_new_core x\<rangle> in
    make_function_contract pre post\<close>

lemma nonzero_i64_test_spec:
  shows \<open>\<Gamma>; nonzero_i64_test x \<Turnstile>\<^sub>F nonzero_i64_test_contract x\<close>
  by (crush_boot f: nonzero_i64_test_def contract: nonzero_i64_test_contract_def) crush_base

lemma nonzeroi64_new_core_values:
  shows \<open>nonzeroi64_new_core 0 = None\<close>
    and \<open>nonzeroi64_new_core (-1) \<noteq> None\<close>
  by (simp_all add: nonzeroi64_new_core_def)

definition range_incl_i8 :: \<open>8 sword \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>range_incl_i8 x \<equiv> FunctionBody \<lbrakk>
    let r = -10_i8 ..= -1_i8;
    r.contains(x)
  \<rbrakk>\<close>

definition range_incl_i8_contract where
  \<open>range_incl_i8_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r \<longleftrightarrow> -10 \<le> sint x \<and> sint x \<le> -1\<rangle> in
    make_function_contract pre post\<close>

text\<open>Crush has a rule for \<^const>\<open>range_new\<close> (\<^verbatim>\<open>wp_range_new\<close>) but none for
\<^const>\<open>range_eq_new\<close>, for unsigned and signed bounds alike, so the inclusive range constructor
has to be unfolded.\<close>

lemma range_incl_i8_spec:
  shows \<open>\<Gamma>; range_incl_i8 x \<Turnstile>\<^sub>F range_incl_i8_contract x\<close>
  by (crush_boot f: range_incl_i8_def contract: range_incl_i8_contract_def)
    (crush_base simp add: range_eq_new_def word_sle_eq)

definition range_incl_u8 :: \<open>8 word \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>range_incl_u8 x \<equiv> FunctionBody \<lbrakk>
    let r = 10_u8 ..= 20_u8;
    r.contains(x)
  \<rbrakk>\<close>

definition range_incl_u8_contract where
  \<open>range_incl_u8_contract x \<equiv>
    let pre  = \<langle>True\<rangle> in
    let post = \<lambda>r. \<langle>r \<longleftrightarrow> 10 \<le> unat x \<and> unat x \<le> 20\<rangle> in
    make_function_contract pre post\<close>

lemma range_incl_u8_spec:
  shows \<open>\<Gamma>; range_incl_u8 x \<Turnstile>\<^sub>F range_incl_u8_contract x\<close>
  by (crush_boot f: range_incl_u8_def contract: range_incl_u8_contract_def)
    (crush_base simp add: range_eq_new_def word_le_nat_alt)


context signed_test_ctx begin

text\<open>A loop over a range with concrete negative bounds.\<close>

definition sum_neg_range :: \<open>('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>sum_neg_range \<equiv> FunctionBody \<lbrakk>
    let mut acc = 0_i32;
    for i in -3_i32 .. 3_i32 {
      acc = *acc + i;
    };
    *acc
  \<rbrakk>\<close>

definition sum_neg_range_contract where
  \<open>sum_neg_range_contract \<equiv>
    let pre  = can_alloc_reference in
    let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = -3\<rangle> in
    make_function_contract pre post\<close>

text\<open>Crush does not unroll a loop over a literal range by itself, for unsigned
(\<open>[Suc 0..<4]\<close>) and signed (\<open>[-3..2]\<close>) bounds alike: \<^verbatim>\<open>crush_base\<close> stops at the
\<open>raw_for_loop\<close> goal. With the recursion equation of the list enumeration as a hint both
prove; the signed loop needs \<^verbatim>\<open>crush_base\<close> to be repeated (one call unrolls two iterations).\<close>

lemma sum_neg_range_spec:
  shows \<open>\<Gamma>; sum_neg_range \<Turnstile>\<^sub>F sum_neg_range_contract\<close>
  apply (crush_boot f: sum_neg_range_def contract: sum_neg_range_contract_def)
  apply (crush_base simp add: upto.simps)+
  done

lemma sum_neg_range_spec_rec1:
  shows \<open>\<Gamma>; sum_neg_range \<Turnstile>\<^sub>F sum_neg_range_contract\<close>
  by (crush_boot f: sum_neg_range_def contract: sum_neg_range_contract_def)
    (crush_base simp add: upto_rec1)

definition sum_pos_range :: \<open>('s, 32 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>sum_pos_range \<equiv> FunctionBody \<lbrakk>
    let mut acc = 0_u32;
    for i in 1_u32 .. 4_u32 {
      acc = *acc + i;
    };
    *acc
  \<rbrakk>\<close>

definition sum_pos_range_contract where
  \<open>sum_pos_range_contract \<equiv>
    let pre  = can_alloc_reference in
    let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = 6\<rangle> in
    make_function_contract pre post\<close>

lemma sum_pos_range_spec:
  shows \<open>\<Gamma>; sum_pos_range \<Turnstile>\<^sub>F sum_pos_range_contract\<close>
  by (crush_boot f: sum_pos_range_def contract: sum_pos_range_contract_def)
    (crush_base simp add: upt_rec)

definition sum_nonneg_range :: \<open>('s, 32 sword, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>sum_nonneg_range \<equiv> FunctionBody \<lbrakk>
    let mut acc = 0_i32;
    for i in 1_i32 .. 4_i32 {
      acc = *acc + i;
    };
    *acc
  \<rbrakk>\<close>

definition sum_nonneg_range_contract where
  \<open>sum_nonneg_range_contract \<equiv>
    let pre  = can_alloc_reference in
    let post = \<lambda>r. can_alloc_reference \<star> \<langle>r = 6\<rangle> in
    make_function_contract pre post\<close>

lemma sum_nonneg_range_spec:
  shows \<open>\<Gamma>; sum_nonneg_range \<Turnstile>\<^sub>F sum_nonneg_range_contract\<close>
  by (crush_boot f: sum_nonneg_range_def contract: sum_nonneg_range_contract_def)
    (crush_base simp add: upto.simps)

end

end
