(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Numeric_Types_Lemmas
  imports Core_Expression_Lemmas Numeric_Types
begin
(*>*)

lemma evaluate_lt_literal [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  assumes \<open>\<not> is_signed TYPE('l)\<close>
  shows \<open>\<lbrakk> c < d \<rbrakk> = \<lbrakk> \<llangle>c < d\<rrangle> \<rbrakk>\<close>
  using assms by (clarsimp simp add: micro_rust_simps comp_lt_def)

lemma evaluate_gt_literal [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  assumes \<open>\<not> is_signed TYPE('l)\<close>
  shows \<open>\<lbrakk> c > d \<rbrakk> = \<lbrakk> \<llangle>c > d\<rrangle> \<rbrakk>\<close>
  using assms by (clarsimp simp add: micro_rust_simps comp_gt_def)

lemma evaluate_ge_literal [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  assumes \<open>\<not> is_signed TYPE('l)\<close>
  shows \<open>\<lbrakk> c >= d \<rbrakk> = \<lbrakk> \<llangle>c \<ge> d\<rrangle> \<rbrakk>\<close>
  using assms by (clarsimp simp add: micro_rust_simps comp_ge_def)

lemma evaluate_le_literal [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  assumes \<open>\<not> is_signed TYPE('l)\<close>
  shows \<open>\<lbrakk> c <= d \<rbrakk> = \<lbrakk> \<llangle>c \<le> d\<rrangle> \<rbrakk>\<close>
  using assms by (clarsimp simp add: micro_rust_simps comp_le_def)

lemma evaluate_word_bitwise_or_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> c | d \<rbrakk> = \<lbrakk> \<llangle>c OR d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_or_pure_def word_bitwise_or_def)

lemma evaluate_word_bitwise_xor_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> c ^ d \<rbrakk> = \<lbrakk> \<llangle>c XOR d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_xor_pure_def word_bitwise_xor_def)

lemma evaluate_word_bitwise_and_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> c & d \<rbrakk> = \<lbrakk> \<llangle>c AND d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_and_pure_def word_bitwise_and_def)

lemma evaluate_word_bitwise_not_literal [micro_rust_simps]:
  shows \<open>\<lbrakk> !d \<rbrakk> = \<lbrakk> \<llangle>NOT d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps word_bitwise_not_pure_def word_bitwise_not_def)

lemma evaluate_word_shift_left_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
  shows \<open>\<lbrakk> c << d \<rbrakk> = \<lbrakk> \<llangle>push_bit (unat d) c\<rrangle> \<rbrakk>\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_left_def 
    word_shift_left_shift64_def
    word_shift_left_pure_def word_shift_left_core_def word_shift_left_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

lemma evaluate_word_shift_right_literal [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
    and \<open>\<not> is_signed TYPE('l0)\<close>
  shows \<open>\<lbrakk> c >> d \<rbrakk> = \<lbrakk> \<llangle>drop_bit (unat d) c\<rrangle> \<rbrakk>\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_right_def 
    word_shift_right_shift64_def
    word_shift_right_pure_def word_shift_right_core_def word_shift_right_as_urust_def 
    option_unwrap_expr_def split!: option.splits)

text\<open>Without an assumption on the signedness, a comparison evaluates to the signedness-aware
comparison of words. This rule lets Crush evaluate comparisons in definitions that are generic in
the length.\<close>

lemma evaluate_lt_literal_word [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  shows \<open>\<lbrakk> c < d \<rbrakk> = \<lbrakk> \<llangle>word_rust_lt c d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps comp_lt_def)

lemma evaluate_gt_literal_word [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  shows \<open>\<lbrakk> c > d \<rbrakk> = \<lbrakk> \<llangle>word_rust_lt d c\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps comp_gt_def)

lemma evaluate_ge_literal_word [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  shows \<open>\<lbrakk> c >= d \<rbrakk> = \<lbrakk> \<llangle>word_rust_le d c\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps comp_ge_def)

lemma evaluate_le_literal_word [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  shows \<open>\<lbrakk> c <= d \<rbrakk> = \<lbrakk> \<llangle>word_rust_le c d\<rrangle> \<rbrakk>\<close>
  by (clarsimp simp add: micro_rust_simps comp_le_def)

lemma evaluate_lt_literal_signed [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  assumes \<open>is_signed TYPE('l)\<close>
  shows \<open>\<lbrakk> c < d \<rbrakk> = \<lbrakk> \<llangle>c <s d\<rrangle> \<rbrakk>\<close>
  using assms by (clarsimp simp add: micro_rust_simps comp_lt_def)

lemma evaluate_gt_literal_signed [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  assumes \<open>is_signed TYPE('l)\<close>
  shows \<open>\<lbrakk> c > d \<rbrakk> = \<lbrakk> \<llangle>d <s c\<rrangle> \<rbrakk>\<close>
  using assms by (clarsimp simp add: micro_rust_simps comp_gt_def)

lemma evaluate_ge_literal_signed [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  assumes \<open>is_signed TYPE('l)\<close>
  shows \<open>\<lbrakk> c >= d \<rbrakk> = \<lbrakk> \<llangle>d \<le>s c\<rrangle> \<rbrakk>\<close>
  using assms by (clarsimp simp add: micro_rust_simps comp_ge_def)

lemma evaluate_le_literal_signed [micro_rust_simps]:
  fixes c d :: \<open>'l::len word\<close>
  assumes \<open>is_signed TYPE('l)\<close>
  shows \<open>\<lbrakk> c <= d \<rbrakk> = \<lbrakk> \<llangle>c \<le>s d\<rrangle> \<rbrakk>\<close>
  using assms by (clarsimp simp add: micro_rust_simps comp_le_def)

lemma evaluate_word_shift_right_literal_signed [micro_rust_simps]:
  fixes c :: \<open>'l0::len word\<close>
    and d :: \<open>64 word\<close>
  assumes \<open>unat d < LENGTH('l0)\<close>
    and \<open>is_signed TYPE('l0)\<close>
  shows \<open>\<lbrakk> c >> d \<rbrakk> = \<lbrakk> \<llangle>signed_drop_bit (unat d) c\<rrangle> \<rbrakk>\<close>
  using assms by (auto simp add: micro_rust_simps word_shift_right_def
    word_shift_right_shift64_def
    word_shift_right_pure_def word_shift_right_core_def word_shift_right_as_urust_def
    option_unwrap_expr_def split!: option.splits)

(*<*)
end
(*>*)
