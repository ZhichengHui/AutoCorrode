(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Signed_Tests_Language
  imports
    Micro_Rust_Std_Lib.StdLib_All
begin

section\<open>Harness\<close>

text\<open>Programs are run with \<^const>\<open>evaluate\<close> on the unit state and the outcome is projected to a
datatype with decidable equality, so that \<^verbatim>\<open>eval\<close> can check the expected result.\<close>

datatype 'v outcome = Val 'v | Ret 'v | Abt \<open>unit abort\<close> | Yld

definition outcome :: \<open>(unit, 'v, 'v, unit, unit prompt, unit prompt_output) continuation \<Rightarrow> 'v outcome\<close> where
  \<open>outcome c \<equiv> case c of Success v _ \<Rightarrow> Val v | Return r _ \<Rightarrow> Ret r | Abort a _ \<Rightarrow> Abt a | Yield _ _ _ \<Rightarrow> Yld\<close>

definition run :: \<open>(unit, 'v, 'v, unit, unit prompt, unit prompt_output) expression \<Rightarrow> 'v outcome\<close> where
  \<open>run e \<equiv> outcome (evaluate e ())\<close>

abbreviation overflow :: \<open>'v outcome\<close> where
  \<open>overflow \<equiv> Abt (Panic overflow_err_msg)\<close>

abbreviation div_zero :: \<open>'v outcome\<close> where
  \<open>div_zero \<equiv> Abt (Panic (String.implode ''division by zero''))\<close>

text\<open>Results are checked by simplification, as in the loop-control tests: \<^verbatim>\<open>run_simps\<close>
unfolds the harness, the evaluation of the monad and the integer operations, and the simplifier
computes the arithmetic on numerals. No code is generated.\<close>

text\<open>A function body that panics panics when called (the counterpart of \<^verbatim>\<open>call_literal\<close>).\<close>

lemma call_panic:
  shows \<open>call (FunctionBody (panic m)) = panic m\<close>
  by (simp add: call_def call_function_body.simps evaluate_def abort_def)

lemmas run_simps = run_def outcome_def micro_rust_simps bind_evaluate Let_def evaluate_loop_step sequence_def
  word_add_no_wrap_def word_add_no_wrap_core_def word_add_no_wrap_as_urust_def
  word_mul_no_wrap_def word_mul_no_wrap_core_def word_mul_no_wrap_as_urust_def
  word_minus_no_wrap_def word_minus_no_wrap_core_def word_minus_no_wrap_as_urust_def
  word_minus_no_wrap_pure_def word_op_no_wrap_pure_def sword_op_no_wrap_pure_def option_unwrap_expr_def
  word_udiv_def word_udiv_core_def word_umod_def word_umod_core_def
  word_shift_right_def word_shift_right_shift64_def word_shift_right_core_def
  word_shift_right_as_urust_def word_shift_right_pure_def
  bind1_def bind2_def two_armed_conditional_def sequence_def sdiv_word_def smod_word_def
  word_sle_eq word_sless_alt
  word_shift_left_def word_shift_left_shift64_def word_shift_left_core_def
  word_shift_left_as_urust_def word_shift_left_pure_def
  signed_divide_int_def signed_modulo_int_def
  word_try_from_fun_def word_try_from_pure_def mask_eq_exp_minus_1
  overflowing_mul_def overflowing_add_def wrapping_add_unsigned_def word_sub_saturating_core_def
  saturating_sub_def checked_mul_core_def checked_add_core_def checked_mul_def checked_add_def
  div_ceil_pure_def div_ceil_def nonzeroi64_new_def nonzeroi64_new_core.abs_eq nonzeroi64_get_def
  nonzerou64_new_def nonzerou64_new_core.abs_eq nonzerou64_get_def cmp_def cmp_pure_def
  is_empty_def contains_def range_into_list_def upto.simps upt_rec
  call_panic urust_eq_def bindlift2_def range_new_def range_eq_new_def ncase_simps
  nonzero_i64_inject_inverse nonzero_u64_inject_inverse

section\<open>Literals and translation\<close>

lemma lit_i8_min: \<open>\<lbrakk> -128_i8 \<rbrakk> = literal (-128 :: 8 sword)\<close> by simp
lemma lit_i8_minus_one: \<open>\<lbrakk> -1_i8 \<rbrakk> = literal (-1 :: 8 sword)\<close> by simp
lemma lit_i8_minus_zero: \<open>\<lbrakk> -0_i8 \<rbrakk> = literal (0 :: 8 sword)\<close> by simp
lemma lit_i8_one: \<open>\<lbrakk> 1_i8 \<rbrakk> = literal (1 :: 8 sword)\<close> by simp
lemma lit_i8_zero: \<open>\<lbrakk> 0_i8 \<rbrakk> = literal (0 :: 8 sword)\<close> by simp
lemma lit_i16: \<open>\<lbrakk> -32768_i16 \<rbrakk> = literal (-32768 :: 16 sword)\<close> by simp
lemma lit_i32: \<open>\<lbrakk> -2147483648_i32 \<rbrakk> = literal (-2147483648 :: 32 sword)\<close> by simp
lemma lit_i64: \<open>\<lbrakk> -9223372036854775808_i64 \<rbrakk> = literal (-9223372036854775808 :: 64 sword)\<close> by simp
lemma lit_isize: \<open>\<lbrakk> -1_isize \<rbrakk> = literal (-1 :: 64 sword)\<close> by simp
lemma lit_isize_zero_one: \<open>\<lbrakk> 0_isize \<rbrakk> = literal (0 :: 64 sword) \<and> \<lbrakk> 1_isize \<rbrakk> = literal (1 :: 64 sword)\<close> by simp
lemma lit_neg_unsuffixed: \<open>\<lbrakk> -5 \<rbrakk> = literal (-5 :: 8 sword)\<close> by simp
lemma lit_neg_one_unsuffixed: \<open>\<lbrakk> -1 \<rbrakk> = literal (-1 :: 32 sword)\<close> by simp
lemma lit_neg_zero_unsuffixed: \<open>\<lbrakk> -0 \<rbrakk> = literal (0 :: 32 sword)\<close> by simp

text\<open>\<^verbatim>\<open>-128_i8\<close> is one literal, not the negation of \<^verbatim>\<open>128_i8\<close> (which would panic).\<close>
lemma lit_i8_min_runs: \<open>run \<lbrakk> -128_i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
text\<open>Unary minus on a non-literal expression translates to \<^const>\<open>word_uminus\<close>.\<close>
lemma uminus_translation:
  fixes x :: \<open>8 sword\<close>
  shows \<open>\<lbrakk> -x \<rbrakk> = word_uminus (literal x)\<close> by simp
lemma uminus_parens_translation:
  fixes x :: \<open>8 sword\<close>
  shows \<open>\<lbrakk> -(x) \<rbrakk> = word_uminus (literal x)\<close> by simp
lemma uminus_shallow_syntax:
  fixes x :: \<open>8 sword\<close>
  shows \<open>(-\<^sub>\<mu> (\<up>x)) = word_uminus (literal x)\<close> by simp

text\<open>Casts translate to the cast combinators at the right target type.\<close>
lemma cast_translation_i8: fixes x :: \<open>32 sword\<close> shows \<open>\<lbrakk> x as i8 \<rbrakk> = ucasti8 (literal x)\<close> by simp
lemma cast_translation_i16: fixes x :: \<open>32 sword\<close> shows \<open>\<lbrakk> x as i16 \<rbrakk> = ucasti16 (literal x)\<close> by simp
lemma cast_translation_i32: fixes x :: \<open>8 sword\<close> shows \<open>\<lbrakk> x as i32 \<rbrakk> = ucasti32 (literal x)\<close> by simp
lemma cast_translation_i64: fixes x :: \<open>8 sword\<close> shows \<open>\<lbrakk> x as i64 \<rbrakk> = ucasti64 (literal x)\<close> by simp
lemma cast_translation_isize: fixes x :: \<open>8 sword\<close> shows \<open>\<lbrakk> x as isize \<rbrakk> = ucasti64 (literal x)\<close> by simp
lemma cast_translation_u8: fixes x :: \<open>8 sword\<close> shows \<open>\<lbrakk> x as u8 \<rbrakk> = ucastu8 (literal x)\<close> by simp

text\<open>Pointer casts.\<close>
context
  fixes p :: \<open>('addr, 'gv) gref\<close>
  fixes prism8 :: \<open>('gv, 8 sword) prism\<close> and prism16 :: \<open>('gv, 16 sword) prism\<close>
    and prism32 :: \<open>('gv, 32 sword) prism\<close> and prism64 :: \<open>('gv, 64 sword) prism\<close>
begin
adhoc_overloading raw_ptr_cast_prism \<rightleftharpoons> prism8 prism16 prism32 prism64
lemma ptr_cast_translation:
  shows \<open>\<lbrakk> p as *const i8 \<rbrakk> = raw_ptr_cast prism8 (literal p)\<close>
    and \<open>\<lbrakk> p as *mut i16 \<rbrakk> = raw_ptr_cast prism16 (literal p)\<close>
    and \<open>\<lbrakk> p as *const i32 \<rbrakk> = raw_ptr_cast prism32 (literal p)\<close>
    and \<open>\<lbrakk> p as *mut i64 \<rbrakk> = raw_ptr_cast prism64 (literal p)\<close>
    and \<open>\<lbrakk> p as *const isize \<rbrakk> = raw_ptr_cast prism64 (literal p)\<close>
    and \<open>\<lbrakk> p as *mut isize \<rbrakk> = raw_ptr_cast prism64 (literal p)\<close>
  by simp_all
end

section\<open>Addition\<close>

lemma add_i8_ok: \<open>run \<lbrakk> 100_i8 + 27_i8 \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma add_i8_neg: \<open>run \<lbrakk> -100_i8 + -28_i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma add_i8_mixed: \<open>run \<lbrakk> -1_i8 + 1_i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma add_i8_min_max: \<open>run \<lbrakk> -128_i8 + 127_i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma add_i8_overflow_pos: \<open>run \<lbrakk> 127_i8 + 1_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_i8_overflow_neg: \<open>run \<lbrakk> -128_i8 + -1_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_i8_overflow_max_max: \<open>run \<lbrakk> 127_i8 + 127_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_i8_zero: \<open>run \<lbrakk> -128_i8 + 0_i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
text\<open>Unsigned view would wrap: \<open>200 + 100\<close> is fine as signed \<open>-56 + 100 = 44\<close>.\<close>
lemma add_i8_signed_not_unsigned: \<open>run \<lbrakk> -56_i8 + 100_i8 \<rbrakk> = Val 44\<close> by (simp add: run_simps)
lemma add_i16_ok: \<open>run \<lbrakk> -32768_i16 + 32767_i16 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma add_i16_overflow: \<open>run \<lbrakk> 32767_i16 + 1_i16 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_i16_underflow: \<open>run \<lbrakk> -32768_i16 + -1_i16 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_i32_ok: \<open>run \<lbrakk> 2147483647_i32 + -1_i32 \<rbrakk> = Val 2147483646\<close> by (simp add: run_simps)
lemma add_i32_overflow: \<open>run \<lbrakk> 2147483647_i32 + 1_i32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_i32_underflow: \<open>run \<lbrakk> -2147483648_i32 + -1_i32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_i64_ok: \<open>run \<lbrakk> -9223372036854775808_i64 + 9223372036854775807_i64 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma add_i64_overflow: \<open>run \<lbrakk> 9223372036854775807_i64 + 1_i64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_i64_underflow: \<open>run \<lbrakk> -9223372036854775808_i64 + -1_i64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_isize_overflow: \<open>run \<lbrakk> 9223372036854775807_isize + 1_isize \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_isize_ok: \<open>run \<lbrakk> -5_isize + 3_isize \<rbrakk> = Val (-2)\<close> by (simp add: run_simps)
text\<open>Unsigned regression.\<close>
lemma add_u8_ok: \<open>run \<lbrakk> 200_u8 + 55_u8 \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma add_u8_overflow: \<open>run \<lbrakk> 255_u8 + 1_u8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_u8_overflow2: \<open>run \<lbrakk> 200_u8 + 100_u8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_u32_overflow: \<open>run \<lbrakk> 4294967295_u32 + 1_u32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_u64_overflow: \<open>run \<lbrakk> 18446744073709551615_u64 + 1_u64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma add_u64_ok: \<open>run \<lbrakk> 18446744073709551614_u64 + 1_u64 \<rbrakk> = Val 18446744073709551615\<close> by (simp add: run_simps)
lemma add_usize_ok: \<open>run \<lbrakk> 1_usize + 2_usize \<rbrakk> = Val 3\<close> by (simp add: run_simps)
section\<open>Subtraction\<close>

lemma sub_i8_ok: \<open>run \<lbrakk> -128_i8 - -128_i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma sub_i8_ok2: \<open>run \<lbrakk> 0_i8 - 127_i8 \<rbrakk> = Val (-127)\<close> by (simp add: run_simps)
lemma sub_i8_ok3: \<open>run \<lbrakk> -1_i8 - 127_i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma sub_i8_ok4: \<open>run \<lbrakk> 0_i8 - -127_i8 \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma sub_i8_neg_result: \<open>run \<lbrakk> 3_i8 - 5_i8 \<rbrakk> = Val (-2)\<close> by (simp add: run_simps)
lemma sub_i8_overflow_neg: \<open>run \<lbrakk> -128_i8 - 1_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma sub_i8_overflow_pos: \<open>run \<lbrakk> 127_i8 - -1_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma sub_i8_overflow_zero_min: \<open>run \<lbrakk> 0_i8 - -128_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma sub_i8_overflow_min_one: \<open>run \<lbrakk> -2_i8 - 127_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma sub_i16_overflow: \<open>run \<lbrakk> -32768_i16 - 1_i16 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma sub_i32_ok: \<open>run \<lbrakk> -2147483648_i32 - -1_i32 \<rbrakk> = Val (-2147483647)\<close> by (simp add: run_simps)
lemma sub_i32_overflow: \<open>run \<lbrakk> 2147483647_i32 - -1_i32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma sub_i64_overflow: \<open>run \<lbrakk> -9223372036854775808_i64 - 1_i64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma sub_i64_ok: \<open>run \<lbrakk> -9223372036854775807_i64 - 1_i64 \<rbrakk> = Val (-9223372036854775808)\<close> by (simp add: run_simps)
lemma sub_isize_ok: \<open>run \<lbrakk> 3_isize - 5_isize \<rbrakk> = Val (-2)\<close> by (simp add: run_simps)
lemma sub_u8_underflow: \<open>run \<lbrakk> 0_u8 - 1_u8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma sub_u8_ok: \<open>run \<lbrakk> 255_u8 - 255_u8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma sub_u64_underflow: \<open>run \<lbrakk> 3_u64 - 5_u64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
section\<open>Multiplication\<close>

lemma mul_i8_ok: \<open>run \<lbrakk> -8_i8 * 16_i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma mul_i8_ok2: \<open>run \<lbrakk> -1_i8 * 127_i8 \<rbrakk> = Val (-127)\<close> by (simp add: run_simps)
lemma mul_i8_ok3: \<open>run \<lbrakk> -1_i8 * -1_i8 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma mul_i8_ok4: \<open>run \<lbrakk> -128_i8 * 1_i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma mul_i8_ok5: \<open>run \<lbrakk> -128_i8 * 0_i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma mul_i8_ok6: \<open>run \<lbrakk> -11_i8 * -11_i8 \<rbrakk> = Val 121\<close> by (simp add: run_simps)
lemma mul_i8_overflow: \<open>run \<lbrakk> -128_i8 * -1_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mul_i8_overflow2: \<open>run \<lbrakk> 64_i8 * 2_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mul_i8_overflow3: \<open>run \<lbrakk> -8_i8 * 17_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mul_i8_overflow4: \<open>run \<lbrakk> -12_i8 * -12_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
text\<open>Unsigned view would be fine: \<open>2 * 100 = 200 < 256\<close>, but as signed \<open>200 > 127\<close>.\<close>
lemma mul_i8_signed_overflow: \<open>run \<lbrakk> 2_i8 * 100_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mul_i16_overflow: \<open>run \<lbrakk> -32768_i16 * -1_i16 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mul_i16_ok: \<open>run \<lbrakk> -181_i16 * 181_i16 \<rbrakk> = Val (-32761)\<close> by (simp add: run_simps)
lemma mul_i32_overflow: \<open>run \<lbrakk> 65536_i32 * 32768_i32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mul_i32_ok: \<open>run \<lbrakk> -65536_i32 * 32768_i32 \<rbrakk> = Val (-2147483648)\<close> by (simp add: run_simps)
lemma mul_i64_overflow: \<open>run \<lbrakk> -9223372036854775808_i64 * -1_i64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mul_i64_ok: \<open>run \<lbrakk> -3037000499_i64 * 3037000499_i64 \<rbrakk> = Val (-9223372030926249001)\<close> by (simp add: run_simps)
lemma mul_isize_ok: \<open>run \<lbrakk> -3_isize * 4_isize \<rbrakk> = Val (-12)\<close> by (simp add: run_simps)
lemma mul_u8_ok: \<open>run \<lbrakk> 2_u8 * 100_u8 \<rbrakk> = Val 200\<close> by (simp add: run_simps)
lemma mul_u8_overflow: \<open>run \<lbrakk> 16_u8 * 16_u8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mul_u64_overflow: \<open>run \<lbrakk> 4294967296_u64 * 4294967296_u64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
section\<open>Division and remainder\<close>

lemma div_i8_pos: \<open>run \<lbrakk> 7_i8 / 2_i8 \<rbrakk> = Val 3\<close> by (simp add: run_simps)
lemma div_i8_neg_dividend: \<open>run \<lbrakk> -7_i8 / 2_i8 \<rbrakk> = Val (-3)\<close> by (simp add: run_simps)
lemma div_i8_neg_divisor: \<open>run \<lbrakk> 7_i8 / -2_i8 \<rbrakk> = Val (-3)\<close> by (simp add: run_simps)
lemma div_i8_both_neg: \<open>run \<lbrakk> -7_i8 / -2_i8 \<rbrakk> = Val 3\<close> by (simp add: run_simps)
lemma div_i8_exact_neg: \<open>run \<lbrakk> -8_i8 / 2_i8 \<rbrakk> = Val (-4)\<close> by (simp add: run_simps)
lemma div_i8_min_by_one: \<open>run \<lbrakk> -128_i8 / 1_i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma div_i8_min_by_two: \<open>run \<lbrakk> -128_i8 / 2_i8 \<rbrakk> = Val (-64)\<close> by (simp add: run_simps)
lemma div_i8_min_by_min: \<open>run \<lbrakk> -128_i8 / -128_i8 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma div_i8_max_by_minus_one: \<open>run \<lbrakk> 127_i8 / -1_i8 \<rbrakk> = Val (-127)\<close> by (simp add: run_simps)
lemma div_i8_one_by_min: \<open>run \<lbrakk> 1_i8 / -128_i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma div_i8_minus_one_by_min: \<open>run \<lbrakk> -1_i8 / -128_i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma div_i8_min_by_minus_one: \<open>run \<lbrakk> -128_i8 / -1_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma div_i8_by_zero: \<open>run \<lbrakk> 5_i8 / 0_i8 \<rbrakk> = div_zero\<close> by (simp add: run_simps)
lemma div_i8_neg_by_zero: \<open>run \<lbrakk> -5_i8 / 0_i8 \<rbrakk> = div_zero\<close> by (simp add: run_simps)
lemma div_i8_min_by_zero: \<open>run \<lbrakk> -128_i8 / 0_i8 \<rbrakk> = div_zero\<close> by (simp add: run_simps)
lemma div_i8_zero_by_neg: \<open>run \<lbrakk> 0_i8 / -5_i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
text\<open>Unsigned reading of \<open>-1 / 2\<close> would give \<open>255 div 2 = 127\<close>.\<close>
lemma div_i8_signed_not_unsigned: \<open>run \<lbrakk> -1_i8 / 2_i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma mod_i8_pos: \<open>run \<lbrakk> 7_i8 % 2_i8 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma mod_i8_neg_dividend: \<open>run \<lbrakk> -7_i8 % 2_i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma mod_i8_neg_divisor: \<open>run \<lbrakk> 7_i8 % -2_i8 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma mod_i8_both_neg: \<open>run \<lbrakk> -7_i8 % -2_i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma mod_i8_neg_dividend3: \<open>run \<lbrakk> -7_i8 % 3_i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma mod_i8_pos_neg3: \<open>run \<lbrakk> 7_i8 % -3_i8 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma mod_i8_min_by_minus_one: \<open>run \<lbrakk> -128_i8 % -1_i8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mod_i8_max_by_minus_one: \<open>run \<lbrakk> 127_i8 % -1_i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma mod_i8_min_by_min: \<open>run \<lbrakk> -128_i8 % -128_i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma mod_i8_min_by_three: \<open>run \<lbrakk> -128_i8 % 3_i8 \<rbrakk> = Val (-2)\<close> by (simp add: run_simps)
lemma mod_i8_min_by_127: \<open>run \<lbrakk> -128_i8 % 127_i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma mod_i8_by_zero: \<open>run \<lbrakk> 5_i8 % 0_i8 \<rbrakk> = div_zero\<close> by (simp add: run_simps)
lemma mod_i8_neg_by_zero: \<open>run \<lbrakk> -5_i8 % 0_i8 \<rbrakk> = div_zero\<close> by (simp add: run_simps)
lemma mod_i8_signed_not_unsigned: \<open>run \<lbrakk> -1_i8 % 2_i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma div_i16_min_by_minus_one: \<open>run \<lbrakk> -32768_i16 / -1_i16 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mod_i16_min_by_minus_one: \<open>run \<lbrakk> -32768_i16 % -1_i16 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma div_i16_neg: \<open>run \<lbrakk> -32768_i16 / 3_i16 \<rbrakk> = Val (-10922)\<close> by (simp add: run_simps)
lemma mod_i16_neg: \<open>run \<lbrakk> -32768_i16 % 3_i16 \<rbrakk> = Val (-2)\<close> by (simp add: run_simps)
lemma div_i32_min_by_minus_one: \<open>run \<lbrakk> -2147483648_i32 / -1_i32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mod_i32_min_by_minus_one: \<open>run \<lbrakk> -2147483648_i32 % -1_i32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma div_i32_neg: \<open>run \<lbrakk> -2147483648_i32 / 7_i32 \<rbrakk> = Val (-306783378)\<close> by (simp add: run_simps)
lemma mod_i32_neg: \<open>run \<lbrakk> -2147483648_i32 % 7_i32 \<rbrakk> = Val (-2)\<close> by (simp add: run_simps)
lemma div_i32_by_zero: \<open>run \<lbrakk> -1_i32 / 0_i32 \<rbrakk> = div_zero\<close> by (simp add: run_simps)
lemma div_i64_min_by_minus_one: \<open>run \<lbrakk> -9223372036854775808_i64 / -1_i64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mod_i64_min_by_minus_one: \<open>run \<lbrakk> -9223372036854775808_i64 % -1_i64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma div_i64_neg: \<open>run \<lbrakk> -7_i64 / 2_i64 \<rbrakk> = Val (-3)\<close> by (simp add: run_simps)
lemma mod_i64_neg: \<open>run \<lbrakk> -7_i64 % 2_i64 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma div_i64_max_by_minus_one: \<open>run \<lbrakk> 9223372036854775807_i64 / -1_i64 \<rbrakk> = Val (-9223372036854775807)\<close> by (simp add: run_simps)
lemma div_isize_min_by_minus_one: \<open>run \<lbrakk> -9223372036854775808_isize / -1_isize \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma mod_isize_neg: \<open>run \<lbrakk> -9_isize % 4_isize \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma div_u8_ok: \<open>run \<lbrakk> 255_u8 / 2_u8 \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma mod_u8_ok: \<open>run \<lbrakk> 255_u8 % 2_u8 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma div_u8_by_zero: \<open>run \<lbrakk> 255_u8 / 0_u8 \<rbrakk> = div_zero\<close> by (simp add: run_simps)
lemma mod_u8_by_zero: \<open>run \<lbrakk> 255_u8 % 0_u8 \<rbrakk> = div_zero\<close> by (simp add: run_simps)
lemma div_u64_ok: \<open>run \<lbrakk> 18446744073709551615_u64 / 18446744073709551615_u64 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
section\<open>Unary minus\<close>

lemma neg_i8_pos: \<open>run \<lbrakk> let x = 5_i8; -x \<rbrakk> = Val (-5)\<close> by (simp add: run_simps)
lemma neg_i8_neg: \<open>run \<lbrakk> let x = -5_i8; -x \<rbrakk> = Val 5\<close> by (simp add: run_simps)
lemma neg_i8_zero: \<open>run \<lbrakk> let x = 0_i8; -x \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma neg_i8_max: \<open>run \<lbrakk> let x = 127_i8; -x \<rbrakk> = Val (-127)\<close> by (simp add: run_simps)
lemma neg_i8_minus_max: \<open>run \<lbrakk> let x = -127_i8; -x \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma neg_i8_min: \<open>run \<lbrakk> let x = -128_i8; -x \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma neg_i16_min: \<open>run \<lbrakk> let x = -32768_i16; -x \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma neg_i32_min: \<open>run \<lbrakk> let x = -2147483648_i32; -x \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma neg_i32_ok: \<open>run \<lbrakk> let x = -2147483647_i32; -x \<rbrakk> = Val 2147483647\<close> by (simp add: run_simps)
lemma neg_i64_min: \<open>run \<lbrakk> let x = -9223372036854775808_i64; -x \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma neg_isize_min: \<open>run \<lbrakk> let x = -9223372036854775808_isize; -x \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma neg_isize_ok: \<open>run \<lbrakk> let x = 9223372036854775807_isize; -x \<rbrakk> = Val (-9223372036854775807)\<close> by (simp add: run_simps)
lemma neg_shallow_min: \<open>run (-\<^sub>\<mu> (\<up>(-128 :: 8 sword))) = overflow\<close> by (simp add: run_simps)
lemma neg_shallow_ok: \<open>run (-\<^sub>\<mu> (\<up>(3 :: 8 sword))) = Val (-3)\<close> by (simp add: run_simps)
lemma neg_double: \<open>run \<lbrakk> let x = 5_i8; -(-x) \<rbrakk> = Val 5\<close> by (simp add: run_simps)
lemma neg_of_sum: \<open>run \<lbrakk> let x = 5_i8; -(x + 1_i8) \<rbrakk> = Val (-6)\<close> by (simp add: run_simps)
lemma neg_then_add: \<open>run \<lbrakk> let x = 5_i8; -x + 1_i8 \<rbrakk> = Val (-4)\<close> by (simp add: run_simps)
lemma neg_then_mul: \<open>run \<lbrakk> let x = 5_i8; -x * 2_i8 \<rbrakk> = Val (-10)\<close> by (simp add: run_simps)
lemma neg_then_sub: \<open>run \<lbrakk> let x = 5_i8; let y = 3_i8; x - -y \<rbrakk> = Val 8\<close> by (simp add: run_simps)
text\<open>Unary minus on an unsigned word: in Rust this is a type error. Here it is \<open>0 - x\<close>, which panics
unless \<open>x = 0\<close>.\<close>
lemma neg_u8: \<open>run \<lbrakk> let x = 5_u8; -x \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma neg_u8_zero: \<open>run \<lbrakk> let x = 0_u8; -x \<rbrakk> = Val 0\<close> by (simp add: run_simps)
section\<open>Shifts and bitwise operations\<close>

lemma shr_i8_neg_arith: \<open>run \<lbrakk> -8_i8 >> 1 \<rbrakk> = Val (-4)\<close> by (simp add: run_simps)
lemma shr_i8_neg_arith2: \<open>run \<lbrakk> -7_i8 >> 1 \<rbrakk> = Val (-4)\<close> by (simp add: run_simps)
lemma shr_i8_minus_one: \<open>run \<lbrakk> -1_i8 >> 1 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma shr_i8_minus_one_7: \<open>run \<lbrakk> -1_i8 >> 7 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma shr_i8_min_7: \<open>run \<lbrakk> -128_i8 >> 7 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma shr_i8_min_1: \<open>run \<lbrakk> -128_i8 >> 1 \<rbrakk> = Val (-64)\<close> by (simp add: run_simps)
lemma shr_i8_max_7: \<open>run \<lbrakk> 127_i8 >> 7 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma shr_i8_pos: \<open>run \<lbrakk> 64_i8 >> 6 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma shr_i8_zero_amount: \<open>run \<lbrakk> -5_i8 >> 0 \<rbrakk> = Val (-5)\<close> by (simp add: run_simps)
lemma shr_i8_width_panics: \<open>run \<lbrakk> -1_i8 >> 8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma shr_i8_pos_width_panics: \<open>run \<lbrakk> 1_i8 >> 8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma shr_i8_large_panics: \<open>run \<lbrakk> 1_i8 >> 100 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma shl_i8_into_sign: \<open>run \<lbrakk> 1_i8 << 7 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shl_i8_out: \<open>run \<lbrakk> 1_i8 << 8 \<rbrakk> = overflow\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shl_i8_neg: \<open>run \<lbrakk> -1_i8 << 1 \<rbrakk> = Val (-2)\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shl_i8_neg_7: \<open>run \<lbrakk> -1_i8 << 7 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shl_i8_lose_bits: \<open>run \<lbrakk> 127_i8 << 1 \<rbrakk> = Val (-2)\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shl_i8_min: \<open>run \<lbrakk> -128_i8 << 1 \<rbrakk> = Val 0\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shl_i8_width_minus_one: \<open>run \<lbrakk> 3_i8 << 7 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shr_i16_neg: \<open>run \<lbrakk> -32768_i16 >> 15 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma shr_i16_neg_4: \<open>run \<lbrakk> -256_i16 >> 4 \<rbrakk> = Val (-16)\<close> by (simp add: run_simps)
lemma shr_i16_width: \<open>run \<lbrakk> -1_i16 >> 16 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma shl_i16_width: \<open>run \<lbrakk> 1_i16 << 16 \<rbrakk> = overflow\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shl_i16_sign: \<open>run \<lbrakk> 1_i16 << 15 \<rbrakk> = Val (-32768)\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shr_i32_neg: \<open>run \<lbrakk> -2147483648_i32 >> 31 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma shr_i32_neg_1: \<open>run \<lbrakk> -2147483648_i32 >> 1 \<rbrakk> = Val (-1073741824)\<close> by (simp add: run_simps)
lemma shr_i32_width: \<open>run \<lbrakk> -1_i32 >> 32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma shl_i32_sign: \<open>run \<lbrakk> 1_i32 << 31 \<rbrakk> = Val (-2147483648)\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shr_i64_neg: \<open>run \<lbrakk> -1_i64 >> 63 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma shr_i64_min: \<open>run \<lbrakk> -9223372036854775808_i64 >> 62 \<rbrakk> = Val (-2)\<close> by (simp add: run_simps)
lemma shr_i64_width: \<open>run \<lbrakk> -1_i64 >> 64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma shl_i64_sign: \<open>run \<lbrakk> 1_i64 << 63 \<rbrakk> = Val (-9223372036854775808)\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shl_i64_width: \<open>run \<lbrakk> 1_i64 << 64 \<rbrakk> = overflow\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shr_isize_neg: \<open>run \<lbrakk> -16_isize >> 2 \<rbrakk> = Val (-4)\<close> by (simp add: run_simps)
lemma shr_isize_width: \<open>run \<lbrakk> -16_isize >> 64 \<rbrakk> = overflow\<close> by (simp add: run_simps)
text\<open>The shift amount is a \<^typ>\<open>64 word\<close>; a signed variable amount is not representable.\<close>
lemma shr_i8_amount_var: \<open>run \<lbrakk> let n = 3_u64; -64_i8 >> n \<rbrakk> = Val (-8)\<close> by (simp add: run_simps)
lemma shr_u8_logical: \<open>run \<lbrakk> 128_u8 >> 7 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma shr_u8_logical2: \<open>run \<lbrakk> 255_u8 >> 1 \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma shr_u8_width: \<open>run \<lbrakk> 255_u8 >> 8 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma shl_u8_ok: \<open>run \<lbrakk> 1_u8 << 7 \<rbrakk> = Val 128\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shl_u8_width: \<open>run \<lbrakk> 1_u8 << 8 \<rbrakk> = overflow\<close> by (simp add: run_simps push_bit_eq_mult)
lemma shr_u64_logical: \<open>run \<lbrakk> 18446744073709551615_u64 >> 63 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma and_i8: \<open>run \<lbrakk> -1_i8 & 15_i8 \<rbrakk> = Val 15\<close> by (simp add: run_simps)
lemma and_i8_neg: \<open>run \<lbrakk> -16_i8 & -1_i8 \<rbrakk> = Val (-16)\<close> by (simp add: run_simps)
lemma or_i8: \<open>run \<lbrakk> -128_i8 | 127_i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma or_i8_2: \<open>run \<lbrakk> 0_i8 | -1_i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma xor_i8: \<open>run \<lbrakk> -1_i8 ^ 127_i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma xor_i8_self: \<open>run \<lbrakk> -128_i8 ^ -128_i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma not_i8: \<open>run \<lbrakk> !(-1_i8) \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma not_i8_zero: \<open>run \<lbrakk> !(0_i8) \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma not_i8_max: \<open>run \<lbrakk> !(127_i8) \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma not_i32_min: \<open>run \<lbrakk> !(-2147483648_i32) \<rbrakk> = Val 2147483647\<close> by (simp add: run_simps)
lemma and_i64: \<open>run \<lbrakk> -1_i64 & 9223372036854775807_i64 \<rbrakk> = Val 9223372036854775807\<close> by (simp add: run_simps)
lemma not_u8: \<open>run \<lbrakk> !(0_u8) \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma xor_u8: \<open>run \<lbrakk> 255_u8 ^ 15_u8 \<rbrakk> = Val 240\<close> by (simp add: run_simps)
section\<open>Comparisons and equality\<close>

lemma lt_i8_neg_pos: \<open>run \<lbrakk> -1_i8 < 0_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma lt_i8_pos_neg: \<open>run \<lbrakk> 0_i8 < -1_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma lt_i8_min_max: \<open>run \<lbrakk> -128_i8 < 127_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma lt_i8_max_min: \<open>run \<lbrakk> 127_i8 < -128_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma lt_i8_min_min: \<open>run \<lbrakk> -128_i8 < -128_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma lt_i8_neg_neg: \<open>run \<lbrakk> -128_i8 < -127_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma lt_i8_neg_neg2: \<open>run \<lbrakk> -1_i8 < -2_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma le_i8_min_min: \<open>run \<lbrakk> -128_i8 <= -128_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma le_i8_neg_pos: \<open>run \<lbrakk> -1_i8 <= 0_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma le_i8_pos_neg: \<open>run \<lbrakk> 0_i8 <= -1_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma le_i8_max_min: \<open>run \<lbrakk> 127_i8 <= -128_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma gt_i8_pos_neg: \<open>run \<lbrakk> 0_i8 > -1_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma gt_i8_neg_pos: \<open>run \<lbrakk> -1_i8 > 0_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma gt_i8_max_min: \<open>run \<lbrakk> 127_i8 > -128_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma gt_i8_min_min: \<open>run \<lbrakk> -128_i8 > -128_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma ge_i8_pos_neg: \<open>run \<lbrakk> 0_i8 >= -1_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma ge_i8_neg_pos: \<open>run \<lbrakk> -1_i8 >= 0_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma ge_i8_min_min: \<open>run \<lbrakk> -128_i8 >= -128_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma ge_i8_min_max: \<open>run \<lbrakk> -128_i8 >= 127_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma eq_i8: \<open>run \<lbrakk> -1_i8 == -1_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma eq_i8_cast: \<open>run \<lbrakk> -1_i8 == 255_u8 as i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma neq_i8: \<open>run \<lbrakk> -1_i8 != 1_i8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma neq_i8_false: \<open>run \<lbrakk> -128_i8 != -128_i8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma lt_i16: \<open>run \<lbrakk> -32768_i16 < 32767_i16 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma gt_i16: \<open>run \<lbrakk> -32768_i16 > 32767_i16 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma lt_i32: \<open>run \<lbrakk> -2147483648_i32 < -1_i32 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma le_i32: \<open>run \<lbrakk> 2147483647_i32 <= -2147483648_i32 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma lt_i64: \<open>run \<lbrakk> -9223372036854775808_i64 < 9223372036854775807_i64 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma ge_i64: \<open>run \<lbrakk> -1_i64 >= 0_i64 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma lt_isize: \<open>run \<lbrakk> -1_isize < 1_isize \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma gt_isize: \<open>run \<lbrakk> -9223372036854775808_isize > 0_isize \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma lt_u8: \<open>run \<lbrakk> 255_u8 < 0_u8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma gt_u8: \<open>run \<lbrakk> 255_u8 > 0_u8 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma le_u8: \<open>run \<lbrakk> 128_u8 <= 127_u8 \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma ge_u32: \<open>run \<lbrakk> 4294967295_u32 >= 1_u32 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma lt_u64: \<open>run \<lbrakk> 1_u64 < 18446744073709551615_u64 \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma lt_u64_false: \<open>run \<lbrakk> 18446744073709551615_u64 < 1_u64 \<rbrakk> = Val False\<close> by (simp add: run_simps)
section\<open>Casts\<close>

subsection\<open>From \<^verbatim>\<open>i8\<close>\<close>
text\<open>Regression: Rust parses \<^verbatim>\<open>-1_i8 as u8\<close> as \<^verbatim>\<open>(-1_i8) as u8\<close>; unary minus binds
tighter than \<^verbatim>\<open>as\<close>.\<close>

lemma cast_i8_m1_u8_unparenthesised: \<open>run \<lbrakk> -1_i8 as u8 \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_i8_m1_u8: \<open>run \<lbrakk> (-1_i8) as u8 \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_i8_m1_u16: \<open>run \<lbrakk> (-1_i8) as u16 \<rbrakk> = Val 65535\<close> by (simp add: run_simps)
lemma cast_i8_m1_u32: \<open>run \<lbrakk> (-1_i8) as u32 \<rbrakk> = Val 4294967295\<close> by (simp add: run_simps)
lemma cast_i8_m1_u64: \<open>run \<lbrakk> (-1_i8) as u64 \<rbrakk> = Val 18446744073709551615\<close> by (simp add: run_simps)
lemma cast_i8_m1_usize: \<open>run \<lbrakk> (-1_i8) as usize \<rbrakk> = Val 18446744073709551615\<close> by (simp add: run_simps)
lemma cast_i8_m1_i8: \<open>run \<lbrakk> (-1_i8) as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i8_m1_i16: \<open>run \<lbrakk> (-1_i8) as i16 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i8_m1_i32: \<open>run \<lbrakk> (-1_i8) as i32 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i8_m1_i64: \<open>run \<lbrakk> (-1_i8) as i64 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i8_m1_isize: \<open>run \<lbrakk> (-1_i8) as isize \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i8_min_u8: \<open>run \<lbrakk> (-128_i8) as u8 \<rbrakk> = Val 128\<close> by (simp add: run_simps)
lemma cast_i8_min_u32: \<open>run \<lbrakk> (-128_i8) as u32 \<rbrakk> = Val 4294967168\<close> by (simp add: run_simps)
lemma cast_i8_min_i16: \<open>run \<lbrakk> (-128_i8) as i16 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma cast_i8_min_i32: \<open>run \<lbrakk> (-128_i8) as i32 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma cast_i8_min_i64: \<open>run \<lbrakk> (-128_i8) as i64 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma cast_i8_min_i8: \<open>run \<lbrakk> (-128_i8) as i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma cast_i8_max_u8: \<open>run \<lbrakk> 127_i8 as u8 \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma cast_i8_max_i16: \<open>run \<lbrakk> 127_i8 as i16 \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma cast_i8_max_u64: \<open>run \<lbrakk> 127_i8 as u64 \<rbrakk> = Val 127\<close> by (simp add: run_simps)
subsection\<open>From \<^verbatim>\<open>u8\<close>\<close>
lemma cast_u8_200_i8: \<open>run \<lbrakk> 200_u8 as i8 \<rbrakk> = Val (-56)\<close> by (simp add: run_simps)
lemma cast_u8_200_i16: \<open>run \<lbrakk> 200_u8 as i16 \<rbrakk> = Val 200\<close> by (simp add: run_simps)
lemma cast_u8_200_i32: \<open>run \<lbrakk> 200_u8 as i32 \<rbrakk> = Val 200\<close> by (simp add: run_simps)
lemma cast_u8_200_i64: \<open>run \<lbrakk> 200_u8 as i64 \<rbrakk> = Val 200\<close> by (simp add: run_simps)
lemma cast_u8_200_isize: \<open>run \<lbrakk> 200_u8 as isize \<rbrakk> = Val 200\<close> by (simp add: run_simps)
lemma cast_u8_200_u16: \<open>run \<lbrakk> 200_u8 as u16 \<rbrakk> = Val 200\<close> by (simp add: run_simps)
lemma cast_u8_200_u64: \<open>run \<lbrakk> 200_u8 as u64 \<rbrakk> = Val 200\<close> by (simp add: run_simps)
lemma cast_u8_255_i8: \<open>run \<lbrakk> 255_u8 as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u8_255_i32: \<open>run \<lbrakk> 255_u8 as i32 \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_u8_128_i8: \<open>run \<lbrakk> 128_u8 as i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma cast_u8_127_i8: \<open>run \<lbrakk> 127_u8 as i8 \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma cast_u8_0_i8: \<open>run \<lbrakk> 0_u8 as i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
subsection\<open>From \<^verbatim>\<open>i16\<close>, \<^verbatim>\<open>u16\<close>\<close>
lemma cast_i16_300_i8: \<open>run \<lbrakk> 300_i16 as i8 \<rbrakk> = Val 44\<close> by (simp add: run_simps)
lemma cast_i16_300_u8: \<open>run \<lbrakk> 300_i16 as u8 \<rbrakk> = Val 44\<close> by (simp add: run_simps)
lemma cast_i16_m300_i8: \<open>run \<lbrakk> (-300_i16) as i8 \<rbrakk> = Val (-44)\<close> by (simp add: run_simps)
lemma cast_i16_m300_u8: \<open>run \<lbrakk> (-300_i16) as u8 \<rbrakk> = Val 212\<close> by (simp add: run_simps)
lemma cast_i16_m1_u16: \<open>run \<lbrakk> (-1_i16) as u16 \<rbrakk> = Val 65535\<close> by (simp add: run_simps)
lemma cast_i16_m1_u32: \<open>run \<lbrakk> (-1_i16) as u32 \<rbrakk> = Val 4294967295\<close> by (simp add: run_simps)
lemma cast_i16_m1_i32: \<open>run \<lbrakk> (-1_i16) as i32 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i16_m1_i64: \<open>run \<lbrakk> (-1_i16) as i64 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i16_min_i8: \<open>run \<lbrakk> (-32768_i16) as i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma cast_i16_min_i32: \<open>run \<lbrakk> (-32768_i16) as i32 \<rbrakk> = Val (-32768)\<close> by (simp add: run_simps)
lemma cast_i16_min_u64: \<open>run \<lbrakk> (-32768_i16) as u64 \<rbrakk> = Val 18446744073709518848\<close> by (simp add: run_simps)
lemma cast_i16_max_i8: \<open>run \<lbrakk> 32767_i16 as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i16_128_i8: \<open>run \<lbrakk> 128_i16 as i8 \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma cast_u16_max_i16: \<open>run \<lbrakk> 65535_u16 as i16 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u16_max_i32: \<open>run \<lbrakk> 65535_u16 as i32 \<rbrakk> = Val 65535\<close> by (simp add: run_simps)
lemma cast_u16_max_i8: \<open>run \<lbrakk> 65535_u16 as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u16_300_i8: \<open>run \<lbrakk> 300_u16 as i8 \<rbrakk> = Val 44\<close> by (simp add: run_simps)
lemma cast_u16_max_i64: \<open>run \<lbrakk> 65535_u16 as i64 \<rbrakk> = Val 65535\<close> by (simp add: run_simps)
subsection\<open>From \<^verbatim>\<open>i32\<close>, \<^verbatim>\<open>u32\<close>\<close>
lemma cast_i32_m1_u8: \<open>run \<lbrakk> (-1_i32) as u8 \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_i32_m1_i8: \<open>run \<lbrakk> (-1_i32) as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i32_m1_u16: \<open>run \<lbrakk> (-1_i32) as u16 \<rbrakk> = Val 65535\<close> by (simp add: run_simps)
lemma cast_i32_m1_i16: \<open>run \<lbrakk> (-1_i32) as i16 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i32_m1_u32: \<open>run \<lbrakk> (-1_i32) as u32 \<rbrakk> = Val 4294967295\<close> by (simp add: run_simps)
lemma cast_i32_m1_u64: \<open>run \<lbrakk> (-1_i32) as u64 \<rbrakk> = Val 18446744073709551615\<close> by (simp add: run_simps)
lemma cast_i32_m1_usize: \<open>run \<lbrakk> (-1_i32) as usize \<rbrakk> = Val 18446744073709551615\<close> by (simp add: run_simps)
lemma cast_i32_m1_i64: \<open>run \<lbrakk> (-1_i32) as i64 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i32_m1_isize: \<open>run \<lbrakk> (-1_i32) as isize \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i32_min_i64: \<open>run \<lbrakk> (-2147483648_i32) as i64 \<rbrakk> = Val (-2147483648)\<close> by (simp add: run_simps)
lemma cast_i32_min_u64: \<open>run \<lbrakk> (-2147483648_i32) as u64 \<rbrakk> = Val 18446744071562067968\<close> by (simp add: run_simps)
lemma cast_i32_min_u32: \<open>run \<lbrakk> (-2147483648_i32) as u32 \<rbrakk> = Val 2147483648\<close> by (simp add: run_simps)
lemma cast_i32_min_i16: \<open>run \<lbrakk> (-2147483648_i32) as i16 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma cast_i32_min_i8: \<open>run \<lbrakk> (-2147483648_i32) as i8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma cast_i32_max_i16: \<open>run \<lbrakk> 2147483647_i32 as i16 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i32_max_u16: \<open>run \<lbrakk> 2147483647_i32 as u16 \<rbrakk> = Val 65535\<close> by (simp add: run_simps)
lemma cast_i32_max_i8: \<open>run \<lbrakk> 2147483647_i32 as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i32_max_i64: \<open>run \<lbrakk> 2147483647_i32 as i64 \<rbrakk> = Val 2147483647\<close> by (simp add: run_simps)
lemma cast_i32_300_u8: \<open>run \<lbrakk> 300_i32 as u8 \<rbrakk> = Val 44\<close> by (simp add: run_simps)
lemma cast_i32_300_i8: \<open>run \<lbrakk> 300_i32 as i8 \<rbrakk> = Val 44\<close> by (simp add: run_simps)
lemma cast_i32_m300_u8: \<open>run \<lbrakk> (-300_i32) as u8 \<rbrakk> = Val 212\<close> by (simp add: run_simps)
lemma cast_i32_m300_i8: \<open>run \<lbrakk> (-300_i32) as i8 \<rbrakk> = Val (-44)\<close> by (simp add: run_simps)
lemma cast_i32_m300_u16: \<open>run \<lbrakk> (-300_i32) as u16 \<rbrakk> = Val 65236\<close> by (simp add: run_simps)
lemma cast_i32_m300_i16: \<open>run \<lbrakk> (-300_i32) as i16 \<rbrakk> = Val (-300)\<close> by (simp add: run_simps)
lemma cast_u32_max_i32: \<open>run \<lbrakk> 4294967295_u32 as i32 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u32_max_i64: \<open>run \<lbrakk> 4294967295_u32 as i64 \<rbrakk> = Val 4294967295\<close> by (simp add: run_simps)
lemma cast_u32_max_u64: \<open>run \<lbrakk> 4294967295_u32 as u64 \<rbrakk> = Val 4294967295\<close> by (simp add: run_simps)
lemma cast_u32_max_isize: \<open>run \<lbrakk> 4294967295_u32 as isize \<rbrakk> = Val 4294967295\<close> by (simp add: run_simps)
lemma cast_u32_max_i16: \<open>run \<lbrakk> 4294967295_u32 as i16 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u32_max_i8: \<open>run \<lbrakk> 4294967295_u32 as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u32_300_u8: \<open>run \<lbrakk> 300_u32 as u8 \<rbrakk> = Val 44\<close> by (simp add: run_simps)
lemma cast_u32_2p31_i32: \<open>run \<lbrakk> 2147483648_u32 as i32 \<rbrakk> = Val (-2147483648)\<close> by (simp add: run_simps)
subsection\<open>From \<^verbatim>\<open>i64\<close>, \<^verbatim>\<open>u64\<close>, \<^verbatim>\<open>isize\<close>, \<^verbatim>\<open>usize\<close>\<close>
lemma cast_i64_m1_i32: \<open>run \<lbrakk> (-1_i64) as i32 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i64_m1_u32: \<open>run \<lbrakk> (-1_i64) as u32 \<rbrakk> = Val 4294967295\<close> by (simp add: run_simps)
lemma cast_i64_m1_i16: \<open>run \<lbrakk> (-1_i64) as i16 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i64_m1_u16: \<open>run \<lbrakk> (-1_i64) as u16 \<rbrakk> = Val 65535\<close> by (simp add: run_simps)
lemma cast_i64_m1_i8: \<open>run \<lbrakk> (-1_i64) as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i64_m1_u8: \<open>run \<lbrakk> (-1_i64) as u8 \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_i64_m1_u64: \<open>run \<lbrakk> (-1_i64) as u64 \<rbrakk> = Val 18446744073709551615\<close> by (simp add: run_simps)
lemma cast_i64_m1_usize: \<open>run \<lbrakk> (-1_i64) as usize \<rbrakk> = Val 18446744073709551615\<close> by (simp add: run_simps)
lemma cast_i64_m1_isize: \<open>run \<lbrakk> (-1_i64) as isize \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i64_m1_i64: \<open>run \<lbrakk> (-1_i64) as i64 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i64_min_i32: \<open>run \<lbrakk> (-9223372036854775808_i64) as i32 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma cast_i64_min_u8: \<open>run \<lbrakk> (-9223372036854775808_i64) as u8 \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma cast_i64_min_u64: \<open>run \<lbrakk> (-9223372036854775808_i64) as u64 \<rbrakk> = Val 9223372036854775808\<close> by (simp add: run_simps)
lemma cast_i64_min_isize: \<open>run \<lbrakk> (-9223372036854775808_i64) as isize \<rbrakk> = Val (-9223372036854775808)\<close> by (simp add: run_simps)
lemma cast_i64_max_i32: \<open>run \<lbrakk> 9223372036854775807_i64 as i32 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_i64_max_u32: \<open>run \<lbrakk> 9223372036854775807_i64 as u32 \<rbrakk> = Val 4294967295\<close> by (simp add: run_simps)
lemma cast_i64_2p31_i32: \<open>run \<lbrakk> 2147483648_i64 as i32 \<rbrakk> = Val (-2147483648)\<close> by (simp add: run_simps)
lemma cast_i64_m2p31m1_i32: \<open>run \<lbrakk> (-2147483649_i64) as i32 \<rbrakk> = Val 2147483647\<close> by (simp add: run_simps)
lemma cast_u64_max_i64: \<open>run \<lbrakk> 18446744073709551615_u64 as i64 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u64_max_isize: \<open>run \<lbrakk> 18446744073709551615_u64 as isize \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u64_max_i32: \<open>run \<lbrakk> 18446744073709551615_u64 as i32 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u64_max_i16: \<open>run \<lbrakk> 18446744073709551615_u64 as i16 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u64_max_i8: \<open>run \<lbrakk> 18446744073709551615_u64 as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_u64_max_u8: \<open>run \<lbrakk> 18446744073709551615_u64 as u8 \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_u64_2p63_i64: \<open>run \<lbrakk> 9223372036854775808_u64 as i64 \<rbrakk> = Val (-9223372036854775808)\<close> by (simp add: run_simps)
lemma cast_u64_300_i8: \<open>run \<lbrakk> 300_u64 as i8 \<rbrakk> = Val 44\<close> by (simp add: run_simps)
lemma cast_isize_m1_usize: \<open>run \<lbrakk> (-1_isize) as usize \<rbrakk> = Val 18446744073709551615\<close> by (simp add: run_simps)
lemma cast_isize_m1_u8: \<open>run \<lbrakk> (-1_isize) as u8 \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_isize_m1_i32: \<open>run \<lbrakk> (-1_isize) as i32 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_isize_m1_i8: \<open>run \<lbrakk> (-1_isize) as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_isize_m1_i64: \<open>run \<lbrakk> (-1_isize) as i64 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_usize_max_isize: \<open>run \<lbrakk> 18446744073709551615_usize as isize \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_usize_max_i8: \<open>run \<lbrakk> 18446744073709551615_usize as i8 \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma cast_usize_300_i16: \<open>run \<lbrakk> 300_usize as i16 \<rbrakk> = Val 300\<close> by (simp add: run_simps)
subsection\<open>Unsigned to unsigned (regression)\<close>
lemma cast_u32_300_u16: \<open>run \<lbrakk> 300_u32 as u16 \<rbrakk> = Val 300\<close> by (simp add: run_simps)
lemma cast_u64_max_u32: \<open>run \<lbrakk> 18446744073709551615_u64 as u32 \<rbrakk> = Val 4294967295\<close> by (simp add: run_simps)
lemma cast_u8_255_u64: \<open>run \<lbrakk> 255_u8 as u64 \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_u16_max_u8: \<open>run \<lbrakk> 65535_u16 as u8 \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_usize_u8: \<open>run \<lbrakk> 257_usize as u8 \<rbrakk> = Val 1\<close> by (simp add: run_simps)
subsection\<open>Casts of computed values and chains\<close>
lemma cast_chain_neg: \<open>run \<lbrakk> let x = -128_i8; (x as i32) + 1_i32 \<rbrakk> = Val (-127)\<close> by (simp add: run_simps)
lemma cast_chain_round_trip: \<open>run \<lbrakk> let x = -1_i8; ((x as u8) as i32) \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_chain_round_trip2: \<open>run \<lbrakk> let x = -1_i8; ((x as i32) as u8) \<rbrakk> = Val 255\<close> by (simp add: run_simps)
lemma cast_chain_u8_i8_i32: \<open>run \<lbrakk> let x = 200_u8; ((x as i8) as i32) \<rbrakk> = Val (-56)\<close> by (simp add: run_simps)
lemma cast_chain_u8_i32_i8: \<open>run \<lbrakk> let x = 200_u8; ((x as i32) as i8) \<rbrakk> = Val (-56)\<close> by (simp add: run_simps)
lemma cast_of_sum: \<open>run \<lbrakk> (100_i8 + 27_i8) as u8 \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma cast_of_overflowing_sum: \<open>run \<lbrakk> (100_i8 + 100_i8) as i32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
text\<open>Rust: unary minus binds tighter than \<^verbatim>\<open>as\<close>, so \<^verbatim>\<open>-x as i32\<close> is \<^verbatim>\<open>(-x) as i32\<close> and
panics for \<open>x = -128_i8\<close>.\<close>
lemma neg_cast_precedence: \<open>run \<lbrakk> let x = -128_i8; -x as i32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma neg_cast_precedence2: \<open>run \<lbrakk> let x = 5_i8; -x as i32 \<rbrakk> = Val (-5)\<close> by (simp add: run_simps)
lemma neg_cast_precedence_parens: \<open>run \<lbrakk> let x = -128_i8; (-x) as i32 \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma neg_cast_precedence_parens2: \<open>run \<lbrakk> let x = 5_i8; (-x) as i32 \<rbrakk> = Val (-5)\<close> by (simp add: run_simps)
section\<open>\<^verbatim>\<open>From\<close> and \<^verbatim>\<open>TryFrom\<close>\<close>

text\<open>The mixfix \<^verbatim>\<open>i64::fromi16\<close> is a HOL identifier of the shallow syntax
(\<^verbatim>\<open>urust_hol_identifier\<close>); it is not accepted as a callee in the \<^verbatim>\<open>\<lbrakk> \<rbrakk>\<close> surface
syntax ("Inner syntax error at i64::fromi16 ( x )"), and neither is the pre-existing
\<^verbatim>\<open>u64::fromu16\<close>. The surface syntax uses the constant names.\<close>
lemma from_i16_neg: \<open>run \<lbrakk> let x = -1_i16; i64_from_i16(x) \<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma from_i16_min: \<open>run \<lbrakk> let x = -32768_i16; i64_from_i16(x) \<rbrakk> = Val (-32768)\<close> by (simp add: run_simps)
lemma from_i16_max: \<open>run \<lbrakk> let x = 32767_i16; i64_from_i16(x) \<rbrakk> = Val 32767\<close> by (simp add: run_simps)
lemma from_i16_hol_id: \<open>run (call (i64::from\<^sub>i\<^sub>1\<^sub>6 (-32768))) = Val (-32768)\<close> by (simp add: run_simps)
lemma from_i16_hol_id_shallow: \<open>run (i64::from\<^sub>i\<^sub>1\<^sub>6 \<langle>\<up>(-1)\<rangle>) = Val (-1)\<close> by (simp add: run_simps)
lemma from_i32_neg: \<open>run \<lbrakk> let x = -2147483648_i32; i64_from_i32(x) \<rbrakk> = Val (-2147483648)\<close> by (simp add: run_simps)
lemma from_i8_neg: \<open>run \<lbrakk> let x = -128_i8; i64_from_i8(x) \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma from_i8_hol: \<open>run (call (i64::from\<^sub>i\<^sub>8 (-1))) = Val (-1)\<close> by (simp add: run_simps)
lemma from_i32_hol: \<open>run (call (i64::from\<^sub>i\<^sub>3\<^sub>2 (-1))) = Val (-1)\<close> by (simp add: run_simps)
lemma from_u16_regression: \<open>run \<lbrakk> let x = 65535_u16; u64_from_u16(x) \<rbrakk> = Val 65535\<close> by (simp add: run_simps)
lemma from_u8_regression: \<open>run (call (u64::from\<^sub>u\<^sub>8 255)) = Val 255\<close> by (simp add: run_simps)
lemma try_i8_from_i64_max: \<open>run \<lbrakk> let x = 127_i64; i8_try_from_i64(x) \<rbrakk> = Val (Some 127)\<close> by (simp add: run_simps)
lemma try_i8_from_i64_over: \<open>run \<lbrakk> let x = 128_i64; i8_try_from_i64(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_i8_from_i64_min: \<open>run \<lbrakk> let x = -128_i64; i8_try_from_i64(x) \<rbrakk> = Val (Some (-128))\<close> by (simp add: run_simps)
lemma try_i8_from_i64_under: \<open>run \<lbrakk> let x = -129_i64; i8_try_from_i64(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_i8_from_i64_m1: \<open>run \<lbrakk> let x = -1_i64; i8_try_from_i64(x) \<rbrakk> = Val (Some (-1))\<close> by (simp add: run_simps)
lemma try_i8_from_i64_i64min: \<open>run \<lbrakk> let x = -9223372036854775808_i64; i8_try_from_i64(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_i16_from_i64: \<open>run \<lbrakk> let x = -32768_i64; i16_try_from_i64(x) \<rbrakk> = Val (Some (-32768))\<close> by (simp add: run_simps)
lemma try_i16_from_i64_under: \<open>run \<lbrakk> let x = -32769_i64; i16_try_from_i64(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_i16_from_i64_over: \<open>run \<lbrakk> let x = 32768_i64; i16_try_from_i64(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_i32_from_i64_max: \<open>run \<lbrakk> let x = 2147483647_i64; i32_try_from_i64(x) \<rbrakk> = Val (Some 2147483647)\<close> by (simp add: run_simps)
lemma try_i32_from_i64_over: \<open>run \<lbrakk> let x = 2147483648_i64; i32_try_from_i64(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_i32_from_i64_min: \<open>run \<lbrakk> let x = -2147483648_i64; i32_try_from_i64(x) \<rbrakk> = Val (Some (-2147483648))\<close> by (simp add: run_simps)
lemma try_i32_from_i64_under: \<open>run \<lbrakk> let x = -2147483649_i64; i32_try_from_i64(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_isize_from_i64_min: \<open>run \<lbrakk> let x = -9223372036854775808_i64; isize_try_from_i64(x) \<rbrakk> = Val (Some (-9223372036854775808))\<close> by (simp add: run_simps)
lemma try_isize_from_i64_max: \<open>run \<lbrakk> let x = 9223372036854775807_i64; isize_try_from_i64(x) \<rbrakk> = Val (Some 9223372036854775807)\<close> by (simp add: run_simps)
lemma try_i32_from_isize: \<open>run \<lbrakk> let x = -1_isize; i32_try_from_isize(x) \<rbrakk> = Val (Some (-1))\<close> by (simp add: run_simps)
lemma try_i16_from_isize_under: \<open>run \<lbrakk> let x = -32769_isize; i16_try_from_isize(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_i8_from_isize: \<open>run \<lbrakk> let x = -128_isize; i8_try_from_isize(x) \<rbrakk> = Val (Some (-128))\<close> by (simp add: run_simps)
lemma try_i16_from_i32_over: \<open>run \<lbrakk> let x = 32768_i32; i16_try_from_i32(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_i16_from_i32_ok: \<open>run \<lbrakk> let x = -32768_i32; i16_try_from_i32(x) \<rbrakk> = Val (Some (-32768))\<close> by (simp add: run_simps)
lemma try_i8_from_i32_under: \<open>run \<lbrakk> let x = -129_i32; i8_try_from_i32(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_i8_from_i32_ok: \<open>run \<lbrakk> let x = 127_i32; i8_try_from_i32(x) \<rbrakk> = Val (Some 127)\<close> by (simp add: run_simps)
lemma try_i8_from_i16_over: \<open>run \<lbrakk> let x = 128_i16; i8_try_from_i16(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_i8_from_i16_ok: \<open>run \<lbrakk> let x = -128_i16; i8_try_from_i16(x) \<rbrakk> = Val (Some (-128))\<close> by (simp add: run_simps)
text\<open>Pure variants and the HOL mixfix names.\<close>
lemma try_pure_i8_from_i64: \<open>i8::try_from\<^sub>i\<^sub>6\<^sub>4 (-129 :: 64 sword) = (None :: 8 sword option)\<close> by (simp add: word_try_from_pure_def)
lemma try_pure_i8_from_i64_ok: \<open>i8::try_from\<^sub>i\<^sub>6\<^sub>4 (-128 :: 64 sword) = Some (-128 :: 8 sword)\<close> by (simp add: word_try_from_pure_def)
lemma try_pure_i32_from_i64: \<open>i32::try_from\<^sub>i\<^sub>6\<^sub>4 (2147483648 :: 64 sword) = (None :: 32 sword option)\<close> by (simp add: word_try_from_pure_def)
text\<open>Mixed-signedness conversions through \<^const>\<open>word_try_from_pure\<close>, following Rust's
\<^verbatim>\<open>u8::try_from(i8)\<close>, \<^verbatim>\<open>i8::try_from(u8)\<close>, \<^verbatim>\<open>u64::try_from(i64)\<close>, \<^verbatim>\<open>i64::try_from(u64)\<close>.\<close>
lemma try_u8_from_i8_neg: \<open>(word_try_from_pure (-1 :: 8 sword) :: 8 word option) = None\<close> by (simp add: word_try_from_pure_def)
lemma try_u8_from_i8_ok: \<open>(word_try_from_pure (127 :: 8 sword) :: 8 word option) = Some 127\<close> by (simp add: word_try_from_pure_def)
lemma try_u8_from_i8_zero: \<open>(word_try_from_pure (0 :: 8 sword) :: 8 word option) = Some 0\<close> by (simp add: word_try_from_pure_def)
lemma try_i8_from_u8_over: \<open>(word_try_from_pure (128 :: 8 word) :: 8 sword option) = None\<close> by (simp add: word_try_from_pure_def)
lemma try_i8_from_u8_200: \<open>(word_try_from_pure (200 :: 8 word) :: 8 sword option) = None\<close> by (simp add: word_try_from_pure_def)
lemma try_i8_from_u8_ok: \<open>(word_try_from_pure (127 :: 8 word) :: 8 sword option) = Some 127\<close> by (simp add: word_try_from_pure_def)
lemma try_u64_from_i64_neg: \<open>(word_try_from_pure (-1 :: 64 sword) :: 64 word option) = None\<close> by (simp add: word_try_from_pure_def)
lemma try_u64_from_i64_max: \<open>(word_try_from_pure (9223372036854775807 :: 64 sword) :: 64 word option) = Some 9223372036854775807\<close> by (simp add: word_try_from_pure_def)
lemma try_i64_from_u64_over: \<open>(word_try_from_pure (9223372036854775808 :: 64 word) :: 64 sword option) = None\<close> by (simp add: word_try_from_pure_def)
lemma try_i64_from_u64_ok: \<open>(word_try_from_pure (9223372036854775807 :: 64 word) :: 64 sword option) = Some 9223372036854775807\<close> by (simp add: word_try_from_pure_def)
lemma try_u32_from_i64_ok: \<open>(word_try_from_pure (4294967295 :: 64 sword) :: 32 word option) = Some 4294967295\<close> by (simp add: word_try_from_pure_def)
lemma try_u32_from_i64_over: \<open>(word_try_from_pure (4294967296 :: 64 sword) :: 32 word option) = None\<close> by (simp add: word_try_from_pure_def)
lemma try_u32_from_i64_neg: \<open>(word_try_from_pure (-1 :: 64 sword) :: 32 word option) = None\<close> by (simp add: word_try_from_pure_def)
lemma try_i32_from_u64_ok: \<open>(word_try_from_pure (2147483647 :: 64 word) :: 32 sword option) = Some 2147483647\<close> by (simp add: word_try_from_pure_def)
lemma try_i32_from_u64_over: \<open>(word_try_from_pure (2147483648 :: 64 word) :: 32 sword option) = None\<close> by (simp add: word_try_from_pure_def)
lemma try_i64_from_u8: \<open>(word_try_from_pure (255 :: 8 word) :: 64 sword option) = Some 255\<close> by (simp add: word_try_from_pure_def)
lemma try_u8_from_i64_ok: \<open>(word_try_from_pure (255 :: 64 sword) :: 8 word option) = Some 255\<close> by (simp add: word_try_from_pure_def)
lemma try_u8_from_i64_over: \<open>(word_try_from_pure (256 :: 64 sword) :: 8 word option) = None\<close> by (simp add: word_try_from_pure_def)
lemma try_i16_from_u16_over: \<open>(word_try_from_pure (32768 :: 16 word) :: 16 sword option) = None\<close> by (simp add: word_try_from_pure_def)
lemma try_i16_from_u8: \<open>(word_try_from_pure (255 :: 8 word) :: 16 sword option) = Some 255\<close> by (simp add: word_try_from_pure_def)
text\<open>Unsigned regression.\<close>
lemma try_u8_from_u64_ok: \<open>run \<lbrakk> let x = 255_u64; u8_try_from_u64(x) \<rbrakk> = Val (Some 255)\<close> by (simp add: run_simps)
lemma try_u8_from_u64_over: \<open>run \<lbrakk> let x = 256_u64; u8_try_from_u64(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_u32_from_u64_over: \<open>run \<lbrakk> let x = 4294967296_u64; u32_try_from_u64(x) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma try_u32_from_u64_ok: \<open>run \<lbrakk> let x = 4294967295_u64; u32_try_from_u64(x) \<rbrakk> = Val (Some 4294967295)\<close> by (simp add: run_simps)
section\<open>Standard library\<close>

subsection\<open>\<^verbatim>\<open>checked_add\<close>, \<^verbatim>\<open>checked_mul\<close>\<close>
lemma checked_add_i8_ok: \<open>run \<lbrakk> let x_1 = -128_i8; x_1.checked_add(127_i8) \<rbrakk> = Val (Some (-1))\<close> by (simp add: run_simps)
lemma checked_add_i8_over: \<open>run \<lbrakk> let x_2 = 127_i8; x_2.checked_add(1_i8) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma checked_add_i8_under: \<open>run \<lbrakk> let x_3 = -128_i8; x_3.checked_add(-1_i8) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma checked_add_i8_neg_ok: \<open>run \<lbrakk> let x_4 = -100_i8; x_4.checked_add(-28_i8) \<rbrakk> = Val (Some (-128))\<close> by (simp add: run_simps)
lemma checked_add_i8_signed: \<open>run \<lbrakk> let x_5 = -56_i8; x_5.checked_add(100_i8) \<rbrakk> = Val (Some 44)\<close> by (simp add: run_simps)
lemma checked_add_i64_over: \<open>run \<lbrakk> let x_6 = 9223372036854775807_i64; x_6.checked_add(1_i64) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma checked_add_i64_under: \<open>run \<lbrakk> let x_7 = -9223372036854775808_i64; x_7.checked_add(-1_i64) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma checked_add_i32_ok: \<open>run \<lbrakk> let x_8 = -2147483648_i32; x_8.checked_add(2147483647_i32) \<rbrakk> = Val (Some (-1))\<close> by (simp add: run_simps)
lemma checked_add_u8_over: \<open>run \<lbrakk> let x_9 = 255_u8; x_9.checked_add(1_u8) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma checked_add_u8_ok: \<open>run \<lbrakk> let x_10 = 200_u8; x_10.checked_add(55_u8) \<rbrakk> = Val (Some 255)\<close> by (simp add: run_simps)
lemma checked_mul_i8_ok: \<open>run \<lbrakk> let x_11 = -8_i8; x_11.checked_mul(16_i8) \<rbrakk> = Val (Some (-128))\<close> by (simp add: run_simps)
lemma checked_mul_i8_over: \<open>run \<lbrakk> let x_12 = -128_i8; x_12.checked_mul(-1_i8) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma checked_mul_i8_over2: \<open>run \<lbrakk> let x_13 = 2_i8; x_13.checked_mul(100_i8) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma checked_mul_i8_neg_ok: \<open>run \<lbrakk> let x_14 = -11_i8; x_14.checked_mul(-11_i8) \<rbrakk> = Val (Some 121)\<close> by (simp add: run_simps)
lemma checked_mul_i64_over: \<open>run \<lbrakk> let x_15 = -9223372036854775808_i64; x_15.checked_mul(-1_i64) \<rbrakk> = Val None\<close> by (simp add: run_simps)
lemma checked_mul_u8_ok: \<open>run \<lbrakk> let x_16 = 2_u8; x_16.checked_mul(100_u8) \<rbrakk> = Val (Some 200)\<close> by (simp add: run_simps)
lemma checked_mul_u8_over: \<open>run \<lbrakk> let x_17 = 16_u8; x_17.checked_mul(16_u8) \<rbrakk> = Val None\<close> by (simp add: run_simps)
subsection\<open>\<^verbatim>\<open>overflowing_add\<close>, \<^verbatim>\<open>overflowing_mul\<close>\<close>
lemma overflowing_add_i8_ok: \<open>run \<lbrakk> let x_1 = -1_i8; x_1.overflowing_add(1_i8) \<rbrakk> = Val (0, False, TNil)\<close> by (simp add: run_simps)
lemma overflowing_add_i8_over: \<open>run \<lbrakk> let x_2 = 127_i8; x_2.overflowing_add(1_i8) \<rbrakk> = Val (-128, True, TNil)\<close> by (simp add: run_simps)
lemma overflowing_add_i8_under: \<open>run \<lbrakk> let x_3 = -128_i8; x_3.overflowing_add(-1_i8) \<rbrakk> = Val (127, True, TNil)\<close> by (simp add: run_simps)
lemma overflowing_add_i8_neg_ok: \<open>run \<lbrakk> let x_4 = -128_i8; x_4.overflowing_add(127_i8) \<rbrakk> = Val (-1, False, TNil)\<close> by (simp add: run_simps)
lemma overflowing_add_i8_unsigned_would_wrap: \<open>run \<lbrakk> let x_5 = -56_i8; x_5.overflowing_add(100_i8) \<rbrakk> = Val (44, False, TNil)\<close> by (simp add: run_simps)
lemma overflowing_add_i64_over: \<open>run \<lbrakk> let x_6 = 9223372036854775807_i64; x_6.overflowing_add(1_i64) \<rbrakk> = Val (-9223372036854775808, True, TNil)\<close> by (simp add: run_simps)
lemma overflowing_add_u8_over: \<open>run \<lbrakk> let x_7 = 255_u8; x_7.overflowing_add(1_u8) \<rbrakk> = Val (0, True, TNil)\<close> by (simp add: run_simps)
lemma overflowing_add_u8_ok: \<open>run \<lbrakk> let x_8 = 200_u8; x_8.overflowing_add(55_u8) \<rbrakk> = Val (255, False, TNil)\<close> by (simp add: run_simps)
lemma overflowing_mul_i8_ok: \<open>run \<lbrakk> let x_9 = -8_i8; x_9.overflowing_mul(16_i8) \<rbrakk> = Val (-128, False, TNil)\<close> by (simp add: run_simps)
lemma overflowing_mul_i8_over: \<open>run \<lbrakk> let x_10 = -128_i8; x_10.overflowing_mul(-1_i8) \<rbrakk> = Val (-128, True, TNil)\<close> by (simp add: run_simps)
lemma overflowing_mul_i8_over2: \<open>run \<lbrakk> let x_11 = 2_i8; x_11.overflowing_mul(100_i8) \<rbrakk> = Val (-56, True, TNil)\<close> by (simp add: run_simps)
lemma overflowing_mul_i8_neg_over: \<open>run \<lbrakk> let x_12 = -12_i8; x_12.overflowing_mul(-12_i8) \<rbrakk> = Val (-112, True, TNil)\<close> by (simp add: run_simps)
lemma overflowing_mul_u8_over: \<open>run \<lbrakk> let x_13 = 16_u8; x_13.overflowing_mul(16_u8) \<rbrakk> = Val (0, True, TNil)\<close> by (simp add: run_simps)
lemma overflowing_mul_u8_ok: \<open>run \<lbrakk> let x_14 = 2_u8; x_14.overflowing_mul(100_u8) \<rbrakk> = Val (200, False, TNil)\<close> by (simp add: run_simps)
subsection\<open>\<^verbatim>\<open>saturating_sub\<close>\<close>
lemma saturating_sub_i8_ok: \<open>run \<lbrakk> let x_1 = 3_i8; x_1.saturating_sub(5_i8) \<rbrakk> = Val (-2)\<close> by (simp add: run_simps)
lemma saturating_sub_i8_min: \<open>run \<lbrakk> let x_2 = -128_i8; x_2.saturating_sub(1_i8) \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma saturating_sub_i8_min2: \<open>run \<lbrakk> let x_3 = -100_i8; x_3.saturating_sub(100_i8) \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma saturating_sub_i8_max: \<open>run \<lbrakk> let x_4 = 127_i8; x_4.saturating_sub(-1_i8) \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma saturating_sub_i8_max2: \<open>run \<lbrakk> let x_5 = 100_i8; x_5.saturating_sub(-100_i8) \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma saturating_sub_i8_exact_min: \<open>run \<lbrakk> let x_6 = -1_i8; x_6.saturating_sub(127_i8) \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma saturating_sub_i8_exact_max: \<open>run \<lbrakk> let x_7 = 0_i8; x_7.saturating_sub(-127_i8) \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma saturating_sub_i8_zero_min: \<open>run \<lbrakk> let x_8 = 0_i8; x_8.saturating_sub(-128_i8) \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma saturating_sub_i64_min: \<open>run \<lbrakk> let x_9 = -9223372036854775808_i64; x_9.saturating_sub(1_i64) \<rbrakk> = Val (-9223372036854775808)\<close> by (simp add: run_simps)
lemma saturating_sub_i64_max: \<open>run \<lbrakk> let x_10 = 9223372036854775807_i64; x_10.saturating_sub(-1_i64) \<rbrakk> = Val 9223372036854775807\<close> by (simp add: run_simps)
lemma saturating_sub_u8_clamp: \<open>run \<lbrakk> let x_11 = 3_u8; x_11.saturating_sub(5_u8) \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma saturating_sub_u8_ok: \<open>run \<lbrakk> let x_12 = 255_u8; x_12.saturating_sub(5_u8) \<rbrakk> = Val 250\<close> by (simp add: run_simps)
subsection\<open>\<^verbatim>\<open>div_ceil\<close>\<close>
lemma div_ceil_i8_pos: \<open>run \<lbrakk> let x_1 = 7_i8; x_1.div_ceil(2_i8) \<rbrakk> = Val 4\<close> by (simp add: run_simps)
lemma div_ceil_i8_exact: \<open>run \<lbrakk> let x_2 = 8_i8; x_2.div_ceil(2_i8) \<rbrakk> = Val 4\<close> by (simp add: run_simps)
lemma div_ceil_i8_neg_dividend: \<open>run \<lbrakk> let x_3 = -7_i8; x_3.div_ceil(2_i8) \<rbrakk> = Val (-3)\<close> by (simp add: run_simps)
lemma div_ceil_i8_neg_divisor: \<open>run \<lbrakk> let x_4 = 7_i8; x_4.div_ceil(-2_i8) \<rbrakk> = Val (-3)\<close> by (simp add: run_simps)
lemma div_ceil_i8_both_neg: \<open>run \<lbrakk> let x_5 = -7_i8; x_5.div_ceil(-2_i8) \<rbrakk> = Val 4\<close> by (simp add: run_simps)
lemma div_ceil_i8_neg_exact: \<open>run \<lbrakk> let x_6 = -8_i8; x_6.div_ceil(2_i8) \<rbrakk> = Val (-4)\<close> by (simp add: run_simps)
lemma div_ceil_i8_max: \<open>run \<lbrakk> let x_7 = 127_i8; x_7.div_ceil(1_i8) \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma div_ceil_i8_max_2: \<open>run \<lbrakk> let x_8 = 127_i8; x_8.div_ceil(2_i8) \<rbrakk> = Val 64\<close> by (simp add: run_simps)
lemma div_ceil_i8_min_2: \<open>run \<lbrakk> let x_9 = -128_i8; x_9.div_ceil(2_i8) \<rbrakk> = Val (-64)\<close> by (simp add: run_simps)
lemma div_ceil_i8_min_3: \<open>run \<lbrakk> let x_10 = -128_i8; x_10.div_ceil(3_i8) \<rbrakk> = Val (-42)\<close> by (simp add: run_simps)
lemma div_ceil_i8_min_minus_one: \<open>run \<lbrakk> let x_11 = -128_i8; x_11.div_ceil(-1_i8) \<rbrakk> = overflow\<close> by (simp add: run_simps)
lemma div_ceil_i8_max_minus_one: \<open>run \<lbrakk> let x_12 = 127_i8; x_12.div_ceil(-1_i8) \<rbrakk> = Val (-127)\<close> by (simp add: run_simps)
lemma div_ceil_i8_zero: \<open>run \<lbrakk> let x_13 = 7_i8; x_13.div_ceil(0_i8) \<rbrakk> = div_zero\<close> by (simp add: run_simps)
lemma div_ceil_i8_one_by_min: \<open>run \<lbrakk> let x_14 = 1_i8; x_14.div_ceil(-128_i8) \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma div_ceil_i8_m1_by_min: \<open>run \<lbrakk> let x_15 = -1_i8; x_15.div_ceil(-128_i8) \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma div_ceil_i8_zero_dividend: \<open>run \<lbrakk> let x_16 = 0_i8; x_16.div_ceil(-5_i8) \<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma div_ceil_i64_neg: \<open>run \<lbrakk> let x_17 = -9223372036854775807_i64; x_17.div_ceil(2_i64) \<rbrakk> = Val (-4611686018427387903)\<close> by (simp add: run_simps)
lemma div_ceil_u8_ok: \<open>run \<lbrakk> let x_18 = 7_u8; x_18.div_ceil(2_u8) \<rbrakk> = Val 4\<close> by (simp add: run_simps)
subsection\<open>\<^verbatim>\<open>wrapping_add_unsigned\<close>\<close>
lemma wrapping_add_unsigned_i8: \<open>run \<lbrakk> let x_1 = -1_i8; x_1.wrapping_add_unsigned(2_u8) \<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma wrapping_add_unsigned_i8_wrap: \<open>run \<lbrakk> let x_2 = 127_i8; x_2.wrapping_add_unsigned(1_u8) \<rbrakk> = Val (-128)\<close> by (simp add: run_simps)
lemma wrapping_add_unsigned_i8_wrap2: \<open>run \<lbrakk> let x_3 = 100_i8; x_3.wrapping_add_unsigned(255_u8) \<rbrakk> = Val 99\<close> by (simp add: run_simps)
lemma wrapping_add_unsigned_i8_min: \<open>run \<lbrakk> let x_4 = -128_i8; x_4.wrapping_add_unsigned(255_u8) \<rbrakk> = Val 127\<close> by (simp add: run_simps)
lemma wrapping_add_unsigned_i64: \<open>run \<lbrakk> let x_5 = -1_i64; x_5.wrapping_add_unsigned(18446744073709551615_u64) \<rbrakk> = Val (-2)\<close> by (simp add: run_simps)
lemma wrapping_add_unsigned_type:
  fixes x :: \<open>8 sword\<close> and y :: \<open>8 word\<close>
  shows \<open>wrapping_add_unsigned x y = FunctionBody (literal (x + ucast y))\<close>
  by (simp add: wrapping_add_unsigned_def)

subsection\<open>\<^verbatim>\<open>cmp\<close>\<close>
lemma cmp_i8_neg_pos: \<open>run \<lbrakk> let x_1 = -1_i8; x_1.cmp(0_i8) == Ordering::Less \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma cmp_i8_pos_neg: \<open>run \<lbrakk> let x_2 = 0_i8; x_2.cmp(-1_i8) == Ordering::Greater \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma cmp_i8_min_max: \<open>run \<lbrakk> let x_3 = -128_i8; x_3.cmp(127_i8) == Ordering::Less \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma cmp_i8_max_min: \<open>run \<lbrakk> let x_4 = 127_i8; x_4.cmp(-128_i8) == Ordering::Greater \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma cmp_i8_eq: \<open>run \<lbrakk> let x_5 = -128_i8; x_5.cmp(-128_i8) == Ordering::Equal \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma cmp_i8_neg_neg: \<open>run \<lbrakk> let x_6 = -2_i8; x_6.cmp(-1_i8) == Ordering::Less \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma cmp_i64_min: \<open>run \<lbrakk> let x_7 = -9223372036854775808_i64; x_7.cmp(0_i64) == Ordering::Less \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma cmp_u8_max: \<open>run \<lbrakk> let x_8 = 255_u8; x_8.cmp(0_u8) == Ordering::Greater \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma cmp_u8_eq: \<open>run \<lbrakk> let x_9 = 5_u8; x_9.cmp(5_u8) == Ordering::Equal \<rbrakk> = Val True\<close> by (simp add: run_simps)
lemma cmp_eq_literal: \<open>run \<lbrakk> let x_10 = -5_i32; x_10.cmp(0_i32) == Ordering::Less \<rbrakk> = Val True\<close> by (simp add: run_simps)
section\<open>Ranges\<close>

lemma range_list_i8_neg: \<open>range_into_list (make_range (-3 :: 8 sword) 3 False) = [-3, -2, -1, 0, 1, 2]\<close> by eval
lemma range_list_i8_neg_incl: \<open>range_into_list (make_range (-3 :: 8 sword) 3 True) = [-3, -2, -1, 0, 1, 2, 3]\<close> by eval
lemma range_list_i8_empty: \<open>range_into_list (make_range (3 :: 8 sword) (-3) False) = []\<close> by eval
lemma range_list_i8_empty_incl: \<open>range_into_list (make_range (3 :: 8 sword) (-3) True) = []\<close> by eval
lemma range_list_i8_empty_eq: \<open>range_into_list (make_range (-3 :: 8 sword) (-3) False) = []\<close> by eval
lemma range_list_i8_single_incl: \<open>range_into_list (make_range (-128 :: 8 sword) (-128) True) = [-128]\<close> by eval
lemma range_list_i8_to_max_incl: \<open>range_into_list (make_range (125 :: 8 sword) 127 True) = [125, 126, 127]\<close> by eval
lemma range_list_i8_to_max_excl: \<open>range_into_list (make_range (125 :: 8 sword) 127 False) = [125, 126]\<close> by eval
lemma range_list_i8_from_min: \<open>range_into_list (make_range (-128 :: 8 sword) (-126) False) = [-128, -127]\<close> by eval
lemma range_list_i8_all_length: \<open>length (range_into_list (make_range (-128 :: 8 sword) 127 True)) = 256\<close> by eval
lemma range_list_i8_neg_only: \<open>range_into_list (make_range (-3 :: 8 sword) (-1) False) = [-3, -2]\<close> by eval
lemma range_list_i64_neg: \<open>range_into_list (make_range (-2 :: 64 sword) 1 True) = [-2, -1, 0, 1]\<close> by eval
lemma range_list_i32_neg_incl: \<open>range_into_list (make_range (-2147483648 :: 32 sword) (-2147483647) True) = [-2147483648, -2147483647]\<close> by eval
lemma range_list_u8_regression: \<open>range_into_list (make_range (253 :: 8 word) 255 True) = [253, 254, 255]\<close> by eval
lemma range_list_u8_regression2: \<open>range_into_list (make_range (0 :: 8 word) 3 False) = [0, 1, 2]\<close> by eval
lemma range_list_u8_regression_empty: \<open>range_into_list (make_range (3 :: 8 word) 0 True) = []\<close> by eval
text\<open>Unsigned reading of the bounds would make \<open>-3..3\<close> (that is \<open>253..3\<close>) empty.\<close>
lemma range_list_i8_simp: \<open>range_into_list (make_range (-3 :: 8 sword) 3 False) = [-3, -2, -1, 0, 1, 2]\<close>
  by (simp add: range_into_list_make_range upto.simps)

lemma for_signed_return: \<open>run \<lbrakk>
  for i in -3_i8..3_i8 {
    if i == 2_i8 { return i; }
  };
  0_i8
\<rbrakk> = Ret 2\<close> by (simp add: run_simps)
lemma for_signed_first: \<open>run \<lbrakk>
  for i in -3_i8..3_i8 {
    return i;
  };
  0_i8
\<rbrakk> = Ret (-3)\<close> by (simp add: run_simps)
lemma for_signed_last_excl: \<open>run \<lbrakk>
  for i in -3_i8..3_i8 {
    if i == 3_i8 { return i; }
  };
  0_i8
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma for_signed_last_incl: \<open>run \<lbrakk>
  for i in -3_i8..=3_i8 {
    if i == 3_i8 { return i; }
  };
  0_i8
\<rbrakk> = Ret 3\<close> by (simp add: run_simps)
lemma for_signed_empty: \<open>run \<lbrakk>
  for i in 3_i8..-3_i8 {
    return i;
  };
  0_i8
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma for_signed_to_max_incl: \<open>run \<lbrakk>
  for i in 126_i8..=127_i8 {
    if i == 127_i8 { return i; }
  };
  0_i8
\<rbrakk> = Ret 127\<close> by (simp add: run_simps)
lemma for_signed_panic_on_neg: \<open>run \<lbrakk>
  for i in -2_i32..2_i32 {
    if i < 0_i32 { panic!("negative") }
  };
  0_i32
\<rbrakk> = Abt (Panic (String.implode ''negative''))\<close> by (simp add: run_simps)
lemma for_signed_i64_neg: \<open>run \<lbrakk>
  for i in -2_i64..0_i64 {
    if i == -1_i64 { return i; }
  };
  7_i64
\<rbrakk> = Ret (-1)\<close> by (simp add: run_simps)
lemma for_unsigned_regression: \<open>run \<lbrakk>
  for i in 253_u8..=255_u8 {
    if i == 255_u8 { return i; }
  };
  0_u8
\<rbrakk> = Ret 255\<close> by (simp add: run_simps)
lemma for_unsigned_regression_empty: \<open>run \<lbrakk>
  for i in 5_u8..3_u8 {
    return i;
  };
  0_u8
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma is_empty_signed_false: \<open>run (call (is_empty (make_range (-3 :: 8 sword) 3 False))) = Val False\<close> by (simp add: run_simps)
lemma is_empty_signed_true: \<open>run (call (is_empty (make_range (3 :: 8 sword) (-3) False))) = Val True\<close> by (simp add: run_simps)
lemma is_empty_signed_incl_eq: \<open>run (call (is_empty (make_range (-3 :: 8 sword) (-3) True))) = Val False\<close> by (simp add: run_simps)
lemma is_empty_signed_excl_eq: \<open>run (call (is_empty (make_range (-3 :: 8 sword) (-3) False))) = Val True\<close> by (simp add: run_simps)
lemma is_empty_signed_incl_true: \<open>run (call (is_empty (make_range (-2 :: 8 sword) (-3) True))) = Val True\<close> by (simp add: run_simps)
lemma is_empty_unsigned: \<open>run (call (is_empty (make_range (253 :: 8 word) 3 False))) = Val True\<close> by (simp add: run_simps)
lemma contains_signed_neg: \<open>run (call (contains (make_range (-3 :: 8 sword) 3 False) (-3))) = Val True\<close> by (simp add: run_simps)
lemma contains_signed_end_excl: \<open>run (call (contains (make_range (-3 :: 8 sword) 3 False) 3)) = Val False\<close> by (simp add: run_simps)
lemma contains_signed_end_incl: \<open>run (call (contains (make_range (-3 :: 8 sword) 3 True) 3)) = Val True\<close> by (simp add: run_simps)
lemma contains_signed_below: \<open>run (call (contains (make_range (-3 :: 8 sword) 3 True) (-4))) = Val False\<close> by (simp add: run_simps)
lemma contains_signed_max: \<open>run (call (contains (make_range (-3 :: 8 sword) 3 True) 127)) = Val False\<close> by (simp add: run_simps)
lemma contains_signed_min: \<open>run (call (contains (make_range (-128 :: 8 sword) 127 True) (-128))) = Val True\<close> by (simp add: run_simps)
lemma contains_unsigned: \<open>run (call (contains (make_range (0 :: 8 word) 3 False) 255)) = Val False\<close> by (simp add: run_simps)
lemma range_syntax_is_empty: \<open>run \<lbrakk> let r_1 = -3_i8..3_i8; r_1.is_empty() \<rbrakk> = Val False\<close> by (simp add: run_simps)
lemma range_syntax_contains: \<open>run \<lbrakk> let r_2 = -3_i8..=3_i8; r_2.contains(-3_i8) \<rbrakk> = Val True\<close> by (simp add: run_simps)

section\<open>Patterns\<close>

subsection\<open>Numeric switch (top-level, unguarded)\<close>
lemma switch_neg: \<open>run \<lbrakk>
  let x = -5_i8;
  match x { -5 \<Rightarrow> 1_i8, -1 \<Rightarrow> 2_i8, 0 \<Rightarrow> 3_i8, 1 \<Rightarrow> 4_i8, 5 \<Rightarrow> 5_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma switch_neg_one: \<open>run \<lbrakk>
  let x = -1_i8;
  match x { -5 \<Rightarrow> 1_i8, -1 \<Rightarrow> 2_i8, 0 \<Rightarrow> 3_i8, 1 \<Rightarrow> 4_i8, 5 \<Rightarrow> 5_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma switch_zero: \<open>run \<lbrakk>
  let x = 0_i8;
  match x { -5 \<Rightarrow> 1_i8, -1 \<Rightarrow> 2_i8, 0 \<Rightarrow> 3_i8, 1 \<Rightarrow> 4_i8, 5 \<Rightarrow> 5_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 3\<close> by (simp add: run_simps)
lemma switch_one: \<open>run \<lbrakk>
  let x = 1_i8;
  match x { -5 \<Rightarrow> 1_i8, -1 \<Rightarrow> 2_i8, 0 \<Rightarrow> 3_i8, 1 \<Rightarrow> 4_i8, 5 \<Rightarrow> 5_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 4\<close> by (simp add: run_simps)
lemma switch_pos: \<open>run \<lbrakk>
  let x = 5_i8;
  match x { -5 \<Rightarrow> 1_i8, -1 \<Rightarrow> 2_i8, 0 \<Rightarrow> 3_i8, 1 \<Rightarrow> 4_i8, 5 \<Rightarrow> 5_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 5\<close> by (simp add: run_simps)
lemma switch_other: \<open>run \<lbrakk>
  let x = -6_i8;
  match x { -5 \<Rightarrow> 1_i8, -1 \<Rightarrow> 2_i8, 0 \<Rightarrow> 3_i8, 1 \<Rightarrow> 4_i8, 5 \<Rightarrow> 5_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma switch_min: \<open>run \<lbrakk>
  let x = -128_i8;
  match x { -128 \<Rightarrow> 1_i8, 127 \<Rightarrow> 2_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma switch_max: \<open>run \<lbrakk>
  let x = 127_i8;
  match x { -128 \<Rightarrow> 1_i8, 127 \<Rightarrow> 2_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma switch_i64_min: \<open>run \<lbrakk>
  let x = -9223372036854775808_i64;
  match x { -9223372036854775808 \<Rightarrow> 1_i64, -1 \<Rightarrow> 2_i64, _ \<Rightarrow> 0_i64 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
text\<open>Unsigned switch: \<open>255\<close> is not \<open>-1\<close> on an unsigned type only if the pattern is read unsigned;
in \<^typ>\<open>8 word\<close>, \<open>-1 = 255\<close> as a word, so the pattern \<^verbatim>\<open>-1\<close> matches \<open>255_u8\<close> (Rust would reject
the program).\<close>
lemma switch_u8_regression: \<open>run \<lbrakk>
  let x = 255_u8;
  match x { 0 \<Rightarrow> 1_u8, 1 \<Rightarrow> 2_u8, 255 \<Rightarrow> 3_u8, _ \<Rightarrow> 0_u8 }
\<rbrakk> = Val 3\<close> by (simp add: run_simps)
lemma switch_u8_regression_one: \<open>run \<lbrakk>
  let x = 1_u8;
  match x { 0 \<Rightarrow> 1_u8, 1 \<Rightarrow> 2_u8, 255 \<Rightarrow> 3_u8, _ \<Rightarrow> 0_u8 }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma switch_u8_regression_other: \<open>run \<lbrakk>
  let x = 7_u8;
  match x { 0 \<Rightarrow> 1_u8, 1 \<Rightarrow> 2_u8, 255 \<Rightarrow> 3_u8, _ \<Rightarrow> 0_u8 }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
subsection\<open>Guarded numeric patterns and fall-through\<close>
lemma guard_neg_fallthrough: \<open>run \<lbrakk>
  let x = -5_i8;
  match x {
    -5 if x > 0_i8 \<Rightarrow> 1_i8,
    -5 if x < 0_i8 \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma guard_neg_fallthrough_to_wildcard: \<open>run \<lbrakk>
  let x = -5_i8;
  match x {
    -5 if x > 0_i8 \<Rightarrow> 1_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma guard_neg_fallthrough_to_other_literal: \<open>run \<lbrakk>
  let x = -5_i8;
  match x {
    -5 if x > 0_i8 \<Rightarrow> 1_i8,
    -1 \<Rightarrow> 2_i8,
    -5 \<Rightarrow> 3_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 3\<close> by (simp add: run_simps)
lemma guard_neg_first_true: \<open>run \<lbrakk>
  let x = -5_i8;
  let y = 1_i8;
  match x {
    -5 if y == 1_i8 \<Rightarrow> 1_i8,
    -5 \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma guard_neg_one: \<open>run \<lbrakk>
  let x = -1_i8;
  match x {
    -1 if x == -1_i8 \<Rightarrow> 1_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma guard_zero_one: \<open>run \<lbrakk>
  let x = 1_i8;
  match x {
    0 if x == 0_i8 \<Rightarrow> 1_i8,
    1 if x == 0_i8 \<Rightarrow> 2_i8,
    1 if x == 1_i8 \<Rightarrow> 3_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 3\<close> by (simp add: run_simps)
lemma guard_u32_regression: \<open>run \<lbrakk>
  let x = 5_u32;
  match x {
    5 if x > 7_u32 \<Rightarrow> 1_u32,
    5 if x > 3_u32 \<Rightarrow> 2_u32,
    _ \<Rightarrow> 0_u32
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma guard_u32_regression_zero: \<open>run \<lbrakk>
  let x = 0_u32;
  match x {
    0 if x > 7_u32 \<Rightarrow> 1_u32,
    0 if x == 0_u32 \<Rightarrow> 2_u32,
    _ \<Rightarrow> 0_u32
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma guard_wildcard_no_match_panics: \<open>run \<lbrakk>
  let x = -5_i8;
  match x {
    -5 if x > 0_i8 \<Rightarrow> 1_i8,
    _ if x > 0_i8 \<Rightarrow> 2_i8,
    _ \<Rightarrow> panic!("none")
  }
\<rbrakk> = Abt (Panic (String.implode ''none''))\<close> by (simp add: run_simps)
subsection\<open>Nested numeric patterns\<close>
lemma nested_some_neg: \<open>run \<lbrakk>
  match Some(-5_i8) {
    Some(-5) \<Rightarrow> 1_i8,
    Some(_) \<Rightarrow> 2_i8,
    None \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma nested_some_neg_other: \<open>run \<lbrakk>
  match Some(-4_i8) {
    Some(-5) \<Rightarrow> 1_i8,
    Some(_) \<Rightarrow> 2_i8,
    None \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma nested_some_min: \<open>run \<lbrakk>
  match Some(-128_i8) {
    Some(-128) \<Rightarrow> 1_i8,
    Some(_) \<Rightarrow> 2_i8,
    None \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma nested_some_neg_one: \<open>run \<lbrakk>
  match Some(-1_i8) {
    Some(-1) \<Rightarrow> 1_i8,
    Some(1) \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma nested_some_one: \<open>run \<lbrakk>
  match Some(1_i8) {
    Some(-1) \<Rightarrow> 1_i8,
    Some(1) \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma nested_some_zero: \<open>run \<lbrakk>
  match Some(0_i8) {
    Some(-1) \<Rightarrow> 1_i8,
    Some(0) \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma nested_some_guard: \<open>run \<lbrakk>
  let y = 3_i8;
  match Some(-5_i8) {
    Some(-5) if y == 0_i8 \<Rightarrow> 1_i8,
    Some(-5) if y == 3_i8 \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma nested_some_some_neg: \<open>run \<lbrakk>
  match Some(Some(-5_i8)) {
    Some(Some(-5)) \<Rightarrow> 1_i8,
    Some(Some(_)) \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma nested_some_u8_regression: \<open>run \<lbrakk>
  match Some(200_u8) {
    Some(200) \<Rightarrow> 1_u8,
    Some(_) \<Rightarrow> 2_u8,
    None \<Rightarrow> 0_u8
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma if_let_neg: \<open>run \<lbrakk>
  if let Some(-5) = Some(-5_i8) { 1_i8 } else { 0_i8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma if_let_neg_no_match: \<open>run \<lbrakk>
  if let Some(-5) = Some(5_i8) { 1_i8 } else { 0_i8 }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
subsection\<open>Tuple patterns\<close>
lemma tuple_neg: \<open>run \<lbrakk>
  match (-5_i32, 2_i32) {
    (-5, b) \<Rightarrow> b,
    (_, b) if b > 0_i32 \<Rightarrow> 1_i32,
    _ \<Rightarrow> 0_i32
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma tuple_neg_second_arm: \<open>run \<lbrakk>
  match (-4_i32, 2_i32) {
    (-5, b) \<Rightarrow> b,
    (_, b) if b > 0_i32 \<Rightarrow> 1_i32,
    _ \<Rightarrow> 0_i32
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma tuple_neg_third_arm: \<open>run \<lbrakk>
  match (-4_i32, -2_i32) {
    (-5, b) \<Rightarrow> b,
    (_, b) if b > 0_i32 \<Rightarrow> 1_i32,
    _ \<Rightarrow> 0_i32
  }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma tuple_both_neg: \<open>run \<lbrakk>
  match (-5_i8, -1_i8) {
    (-5, -1) \<Rightarrow> 1_i8,
    (-5, _) \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma tuple_both_neg_partial: \<open>run \<lbrakk>
  match (-5_i8, 1_i8) {
    (-5, -1) \<Rightarrow> 1_i8,
    (-5, _) \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma tuple_guard_fallthrough: \<open>run \<lbrakk>
  match (-5_i8, 1_i8) {
    (-5, b) if b == 0_i8 \<Rightarrow> 1_i8,
    (-5, b) if b == 1_i8 \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
text\<open>Regression: arms after an irrefutable arm are unreachable and accepted.\<close>
text\<open>Regression: the guard is evaluated only when the pattern matches (here it would divide by
zero).\<close>
lemma guard_after_pattern: \<open>run \<lbrakk>
  match 6_i8 {
    5 if 1_i8 / 0_i8 == 0_i8 \<Rightarrow> 1_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma guard_after_pattern_nested: \<open>run \<lbrakk>
  match Some(6_i8) {
    Some(5) if 1_i8 / 0_i8 == 0_i8 \<Rightarrow> 1_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma guard_after_pattern_match: \<open>run \<lbrakk>
  match 5_i8 {
    5 if 1_i8 / 0_i8 == 0_i8 \<Rightarrow> 1_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = div_zero\<close> by (simp add: run_simps)

lemma tuple_irrefutable_then_wildcard: \<open>run \<lbrakk>
  match (1_i8, -2_i8) {
    (a, b) \<Rightarrow> a + b,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val (-1)\<close> by (simp add: run_simps)
lemma tuple_irrefutable_only: \<open>run \<lbrakk>
  match (1_i8, -2_i8) {
    (a, b) \<Rightarrow> a - b
  }
\<rbrakk> = Val 3\<close> by (simp add: run_simps)
lemma tuple_irrefutable_guard_then_wildcard: \<open>run \<lbrakk>
  match (1_i8, -2_i8) {
    (a, b) if a > b \<Rightarrow> a,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma tuple_irrefutable_guard_false_then_wildcard: \<open>run \<lbrakk>
  match (1_i8, -2_i8) {
    (a, b) if a < b \<Rightarrow> a,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma tuple_nested_neg: \<open>run \<lbrakk>
  match ((-1_i8, 2_i8), -3_i8) {
    ((-1, b), -3) \<Rightarrow> b,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma tuple_unsigned_regression: \<open>run \<lbrakk>
  match (5_u32, 2_u32) {
    (5, b) \<Rightarrow> b,
    _ \<Rightarrow> 0_u32
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma tuple_unsigned_regression_guard: \<open>run \<lbrakk>
  match (5_u32, 2_u32) {
    (5, b) if b > 3_u32 \<Rightarrow> b,
    (5, b) if b > 1_u32 \<Rightarrow> b + 10_u32,
    _ \<Rightarrow> 0_u32
  }
\<rbrakk> = Val 12\<close> by (simp add: run_simps)
subsection\<open>Range patterns\<close>
text\<open>Regression: range patterns at the top level of a match arm.\<close>
lemma range_pat_top_level: \<open>run \<lbrakk>
  let x = 250_u8;
  match x { 250..=255 \<Rightarrow> 1_u8, _ \<Rightarrow> 0_u8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma range_pat_top_level_signed: \<open>run \<lbrakk>
  let x = -3_i8;
  match x { -5..=-1 \<Rightarrow> 1_i8, 0..10 \<Rightarrow> 2_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma range_pat_top_level_signed_guard: \<open>run \<lbrakk>
  let x = 4_i8;
  match x { -5..=-1 \<Rightarrow> 1_i8, 0..10 if x > 3_i8 \<Rightarrow> 2_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma range_pat_bounds_0_1: \<open>run \<lbrakk>
  let x = 1_u8;
  match x { 0..1 \<Rightarrow> 1_u8, 1..=1 \<Rightarrow> 2_u8, _ \<Rightarrow> 0_u8 }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma range_pat_bound_neg_one_nested: \<open>run \<lbrakk>
  match Some(-1_i8) { Some(-1..=0) \<Rightarrow> 1_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma range_pat_unsigned_regression: \<open>run \<lbrakk>
  let x = 250_u8;
  match Some(x) { Some(250..=255) \<Rightarrow> 1_u8, _ \<Rightarrow> 0_u8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma range_pat_unsigned_regression_miss: \<open>run \<lbrakk>
  let x = 249_u8;
  match Some(x) { Some(250..=255) \<Rightarrow> 1_u8, _ \<Rightarrow> 0_u8 }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
datatype spoint = SPoint (sx: \<open>8 sword\<close>) (sy: \<open>8 sword\<close>)

section\<open>Code generation\<close>

definition i8_arith :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> (unit, 8 sword, 8 sword, unit, unit prompt, unit prompt_output) expression\<close> where
  \<open>i8_arith x y \<equiv> \<lbrakk>
     let a = x + y;
     let b = a - y;
     let c = b * y;
     let d = c / y;
     let e = d % y;
     let f = -e;
     let g = f >> 1;
     let h = g << 1;
     let i = h & y;
     let j = i | y;
     let k = j ^ y;
     let l = !k;
     if l < x && l <= y && l > x && l >= y && l == x && l != y { l } else { (l as i32) as i8 }
  \<rbrakk>\<close>

definition i64_stdlib :: \<open>64 sword \<Rightarrow> 64 word \<Rightarrow> (unit, 64 sword, 64 sword, unit, unit prompt, unit prompt_output) expression\<close> where
  \<open>i64_stdlib x y \<equiv> \<lbrakk>
     let a = x.checked_add(x);
     let b = x.checked_mul(x);
     let c = x.overflowing_add(x);
     let d = x.overflowing_mul(x);
     let e = x.saturating_sub(x);
     let f = x.div_ceil(x);
     let g = x.wrapping_add_unsigned(y);
     let n = NonZeroI64::new(x);
     let r = (x..=x).contains(x);
     let s = (x..x).is_empty();
     let t = i8_try_from_i64(x);
     for i in x..x { () };
     x
  \<rbrakk>\<close>

definition i8_casts :: \<open>8 sword \<Rightarrow> 8 word \<Rightarrow> (unit, 64 sword \<times> 64 word \<times> tnil, 64 sword \<times> 64 word \<times> tnil, unit, unit prompt, unit prompt_output) expression\<close> where
  \<open>i8_casts x y \<equiv> \<lbrakk>
     ((x as i16) as i32 as i64 + (y as i8) as i64 + (y as isize), (x as u8) as u64 + (y as u16) as u32 as u64)
  \<rbrakk>\<close>

text\<open>Regression: code generation of \<^verbatim>\<open>NonZeroI64::new\<close>.\<close>
export_code i8_arith i64_stdlib i8_casts run outcome checking SML
export_code i8_arith i64_stdlib i8_casts run in SML
text\<open>Constants that branch on \<^const>\<open>is_signed\<close> have code only at concrete lengths, through
\<^verbatim>\<open>code_unfold\<close>; they are exported through monomorphic definitions.\<close>

definition cg_lt8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> bool\<close> where \<open>cg_lt8 \<equiv> word_rust_lt\<close>
definition cg_le16 :: \<open>16 sword \<Rightarrow> 16 sword \<Rightarrow> bool\<close> where \<open>cg_le16 \<equiv> word_rust_le\<close>
definition cg_cast_s8_u32 :: \<open>8 sword \<Rightarrow> 32 word\<close> where \<open>cg_cast_s8_u32 \<equiv> word_rust_cast\<close>
definition cg_cast_u8_s32 :: \<open>8 word \<Rightarrow> 32 sword\<close> where \<open>cg_cast_u8_s32 \<equiv> word_rust_cast\<close>
definition cg_try_s64_s8 :: \<open>64 sword \<Rightarrow> 8 sword option\<close> where \<open>cg_try_s64_s8 \<equiv> word_try_from_pure\<close>
definition cg_add8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> 8 sword option\<close> where \<open>cg_add8 \<equiv> word_add_no_wrap_pure\<close>
definition cg_mul8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> 8 sword option\<close> where \<open>cg_mul8 \<equiv> word_mul_no_wrap_pure\<close>
definition cg_sub8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> 8 sword option\<close> where \<open>cg_sub8 \<equiv> word_minus_no_wrap_pure\<close>
definition cg_shr8 :: \<open>8 sword \<Rightarrow> 64 word \<Rightarrow> 8 sword option\<close> where \<open>cg_shr8 \<equiv> word_shift_right_pure\<close>
definition cg_cmp8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> StdLib_Ordering.ordering\<close> where \<open>cg_cmp8 \<equiv> cmp_pure\<close>
definition cg_range8 :: \<open>8 sword range \<Rightarrow> 8 sword list\<close> where \<open>cg_range8 \<equiv> range_into_list\<close>
definition cg_checked_add8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> 8 sword option\<close> where \<open>cg_checked_add8 \<equiv> checked_add_core\<close>
definition cg_div_ceil8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> 8 sword\<close> where \<open>cg_div_ceil8 \<equiv> div_ceil_pure\<close>
definition cg_sat_sub8 :: \<open>8 sword \<Rightarrow> 8 sword \<Rightarrow> 8 sword\<close> where \<open>cg_sat_sub8 \<equiv> word_sub_saturating_core\<close>

export_code cg_lt8 cg_le16 cg_cast_s8_u32 cg_cast_u8_s32 cg_try_s64_s8 cg_add8 cg_mul8 cg_sub8 cg_shr8 cg_cmp8 cg_range8 cg_checked_add8 cg_div_ceil8 cg_sat_sub8 in SML

text\<open>Regression: code generation of programs with \<^verbatim>\<open>&&\<close> and \<^verbatim>\<open>||\<close>.\<close>
value [code] \<open>run (i8_arith (-128) (-1))\<close>
lemma i8_arith_run: \<open>run (i8_arith 3 (-1)) = Val (-1)\<close> by (simp add: run_simps i8_arith_def)
lemma i8_arith_run_overflow: \<open>run (i8_arith 127 1) = overflow\<close> by (simp add: run_simps i8_arith_def)
lemma i64_stdlib_run: \<open>run (i64_stdlib (-9223372036854775808) 1) = Val (-9223372036854775808)\<close> by (simp add: run_simps i64_stdlib_def)
text\<open>Regression: generated code for unsigned 64-bit arithmetic runs quickly (natural numbers are
target-language integers).\<close>
lemma add_u64_eval: \<open>run \<lbrakk> 18446744073709551614_u64 + 1_u64 \<rbrakk> = Val 18446744073709551615\<close> by eval
lemma add_u64_overflow_eval: \<open>run \<lbrakk> 18446744073709551615_u64 + 1_u64 \<rbrakk> = overflow\<close> by eval
lemma add_usize_eval: \<open>run \<lbrakk> 1_usize + 2_usize \<rbrakk> = Val 3\<close> by eval

lemma i8_casts_run: \<open>run (i8_casts (-1) 200) = Val (143, 455, TNil)\<close> by (simp add: run_simps i8_casts_def)
value [code] \<open>(word_rust_cast (-1 :: 8 sword) :: 32 word)\<close>
value [code] \<open>word_rust_lt (-1 :: 8 sword) 0\<close>
value [code] \<open>sword_op_no_wrap_pure (+) (127 :: 8 sword) 1\<close>

section\<open>HOL-level evaluation by the simplifier\<close>

lemma simp_is_signed: \<open>is_signed TYPE(8 signed) \<and> \<not> is_signed TYPE(8) \<and> \<not> is_signed TYPE(64) \<and> is_signed TYPE(64 signed)\<close> by simp
lemma simp_word_rust_lt_signed: \<open>word_rust_lt (-1 :: 8 sword) 0\<close> by simp
lemma simp_word_rust_lt_unsigned: \<open>\<not> word_rust_lt (-1 :: 8 word) 0\<close> by simp
lemma simp_word_rust_le_signed: \<open>word_rust_le (-128 :: 8 sword) 127\<close> by simp
lemma simp_word_rust_le_unsigned: \<open>\<not> word_rust_le (128 :: 8 word) 127\<close> by simp
lemma simp_word_rust_cast_signed: \<open>(word_rust_cast (-1 :: 8 sword) :: 32 word) = 4294967295\<close> by simp
lemma simp_word_rust_cast_unsigned: \<open>(word_rust_cast (200 :: 8 word) :: 32 sword) = 200\<close> by simp
lemma simp_word_rust_cast_signed_narrow: \<open>(word_rust_cast (-300 :: 16 sword) :: 8 sword) = -44\<close> by simp
lemma simp_add_pure_signed_over: \<open>word_add_no_wrap_pure (127 :: 8 sword) 1 = None\<close> by (simp add: sword_op_no_wrap_pure_def)
lemma simp_add_pure_signed_ok: \<open>word_add_no_wrap_pure (-128 :: 8 sword) 127 = Some (-1)\<close> by (simp add: sword_op_no_wrap_pure_def)
lemma simp_add_pure_unsigned_over: \<open>word_add_no_wrap_pure (255 :: 8 word) 1 = None\<close> by (simp add: word_op_no_wrap_pure_def)
lemma simp_add_pure_unsigned_ok: \<open>word_add_no_wrap_pure (200 :: 8 word) 55 = Some 255\<close> by (simp add: word_op_no_wrap_pure_def)
lemma simp_mul_pure_signed_over: \<open>word_mul_no_wrap_pure (-128 :: 8 sword) (-1) = None\<close> by (simp add: sword_op_no_wrap_pure_def)
lemma simp_mul_pure_signed_ok: \<open>word_mul_no_wrap_pure (-8 :: 8 sword) 16 = Some (-128)\<close> by (simp add: sword_op_no_wrap_pure_def)
lemma simp_minus_pure_signed_over: \<open>word_minus_no_wrap_pure (-128 :: 8 sword) 1 = None\<close> by (simp add: word_minus_no_wrap_pure_def sword_op_no_wrap_pure_def)
lemma simp_minus_pure_signed_ok: \<open>word_minus_no_wrap_pure (3 :: 8 sword) 5 = Some (-2)\<close> by (simp add: word_minus_no_wrap_pure_def sword_op_no_wrap_pure_def)
lemma simp_minus_pure_unsigned_under: \<open>word_minus_no_wrap_pure (3 :: 8 word) 5 = None\<close> by (simp add: word_minus_no_wrap_pure_def)
lemma simp_shift_right_signed: \<open>word_shift_right_pure (-8 :: 8 sword) (1 :: 64 word) = Some (-4)\<close> by (simp add: word_shift_right_pure_def)
lemma simp_shift_right_signed_over: \<open>word_shift_right_pure (-8 :: 8 sword) (8 :: 64 word) = None\<close> by (simp add: word_shift_right_pure_def)
lemma simp_shift_right_unsigned: \<open>word_shift_right_pure (128 :: 8 word) (7 :: 64 word) = Some 1\<close> by (simp add: word_shift_right_pure_def)
lemma simp_udiv_signed_min: \<open>word_udiv_core (-128 :: 8 sword) (-1) = (panic overflow_err_msg :: (unit, 8 sword, unit, unit, unit, unit) expression)\<close> by (simp add: word_udiv_core_def)
lemma simp_udiv_signed_zero: \<open>word_udiv_core (-128 :: 8 sword) 0 = (panic (String.implode ''division by zero'') :: (unit, 8 sword, unit, unit, unit, unit) expression)\<close> by (simp add: word_udiv_core_def)
lemma simp_udiv_signed: \<open>word_udiv_core (-7 :: 8 sword) 2 = (literal (-3) :: (unit, 8 sword, unit, unit, unit, unit) expression)\<close> by (simp add: word_udiv_core_def)
lemma simp_umod_signed: \<open>word_umod_core (-7 :: 8 sword) 2 = (literal (-1) :: (unit, 8 sword, unit, unit, unit, unit) expression)\<close> by (simp add: word_umod_core_def)
lemma simp_umod_signed_min: \<open>word_umod_core (-128 :: 8 sword) (-1) = (panic overflow_err_msg :: (unit, 8 sword, unit, unit, unit, unit) expression)\<close> by (simp add: word_umod_core_def)
lemma simp_udiv_unsigned: \<open>word_udiv_core (255 :: 8 word) 2 = (literal 127 :: (unit, 8 word, unit, unit, unit, unit) expression)\<close> by (simp add: word_udiv_core_def)
lemma simp_try_from_signed: \<open>(word_try_from_pure (-129 :: 64 sword) :: 8 sword option) = None\<close> by (simp add: word_try_from_pure_def)
lemma simp_try_from_signed_ok: \<open>(word_try_from_pure (-128 :: 64 sword) :: 8 sword option) = Some (-128)\<close> by (simp add: word_try_from_pure_def)
lemma simp_try_from_unsigned: \<open>(word_try_from_pure (256 :: 64 word) :: 8 word option) = None\<close> by (simp add: word_try_from_pure_def)
lemma simp_checked_add_signed: \<open>checked_add_core (127 :: 8 sword) 1 = None\<close> by (simp add: checked_add_core_def)
lemma simp_checked_mul_signed: \<open>checked_mul_core (-128 :: 8 sword) (-1) = None\<close> by (simp add: checked_mul_core_def)
lemma simp_saturating_signed: \<open>word_sub_saturating_core (-128 :: 8 sword) 1 = -128\<close> by (simp add: word_sub_saturating_core_def)
lemma simp_saturating_signed_max: \<open>word_sub_saturating_core (127 :: 8 sword) (-1) = 127\<close> by (simp add: word_sub_saturating_core_def)
lemma simp_div_ceil_signed: \<open>div_ceil_pure (-7 :: 8 sword) 2 = -3\<close> by (simp add: div_ceil_pure_def)
lemma simp_div_ceil_unsigned: \<open>div_ceil_pure (7 :: 8 word) 2 = 4\<close> by (simp add: div_ceil_pure_def)
lemma simp_sword_op: \<open>sword_op_no_wrap_pure (+) (-1 :: 8 sword) (-128) = None\<close> by (simp add: sword_op_no_wrap_pure_def)

text\<open>The \<mu>Rust simplifier (\<^verbatim>\<open>micro_rust_simps\<close>) evaluates the signedness premise at concrete types.\<close>
lemma urust_simp_comp_lt_signed:
  fixes x y :: \<open>8 sword\<close>
  shows \<open>\<lbrakk> x < y \<rbrakk> = bindlift2 (\<lambda>a b. a <s b) (literal x) (literal y)\<close>
  by (simp add: comp_lt_def word_rust_lt_def[abs_def])
lemma urust_simp_comp_lt_unsigned:
  fixes x y :: \<open>8 word\<close>
  shows \<open>\<lbrakk> x < y \<rbrakk> = bindlift2 (\<lambda>a b. a < b) (literal x) (literal y)\<close>
  by (simp add: comp_lt_def word_rust_lt_def[abs_def])
lemma urust_simp_cast_signed:
  fixes x :: \<open>8 sword\<close>
  shows \<open>\<lbrakk> x as u32 \<rbrakk> = bind1 (literal \<circ> scast) (literal x)\<close>
  by (simp add: micro_rust_simps)
lemma urust_simp_cast_unsigned:
  fixes x :: \<open>8 word\<close>
  shows \<open>\<lbrakk> x as i32 \<rbrakk> = bind1 (literal \<circ> ucast) (literal x)\<close>
  by (simp add: micro_rust_simps)

section\<open>Deferred tests (each of the following was uncertain to parse; kept last so that an error does not stop the rest)\<close>

subsection\<open>Struct patterns with literal fields\<close>


lemma struct_pat_neg_field: \<open>run \<lbrakk>
  match \<llangle>SPoint (-5) 3\<rrangle> {
    SPoint { sx: -5, sy: q } \<Rightarrow> q,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 3\<close> by (simp add: run_simps)
lemma struct_pat_neg_field_miss: \<open>run \<lbrakk>
  match \<llangle>SPoint (-4) 3\<rrangle> {
    SPoint { sx: -5, sy: q } \<Rightarrow> q,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma struct_pat_two_literals: \<open>run \<lbrakk>
  match \<llangle>SPoint (-5) (-1)\<rrangle> {
    SPoint { sx: -5, sy: -1 } \<Rightarrow> 1_i8,
    SPoint { sx: -5, sy: _ } \<Rightarrow> 2_i8,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma struct_pat_irrefutable_then_wildcard: \<open>run \<lbrakk>
  match \<llangle>SPoint (-5) 3\<rrangle> {
    SPoint { sx: p, sy: q } \<Rightarrow> p + q,
    _ \<Rightarrow> 0_i8
  }
\<rbrakk> = Val (-2)\<close> by (simp add: run_simps)
subsection\<open>\<^verbatim>\<open>NonZeroI64\<close>\<close>
lemma nonzero_i64_zero: \<open>run \<lbrakk>
  match NonZeroI64::new(0_i64) {
    None \<Rightarrow> 0_i64,
    Some(nz) \<Rightarrow> nonzeroi64_get(nz)
  }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma nonzero_i64_neg: \<open>run \<lbrakk>
  match NonZeroI64::new(-5_i64) {
    None \<Rightarrow> 0_i64,
    Some(nz) \<Rightarrow> nonzeroi64_get(nz)
  }
\<rbrakk> = Val (-5)\<close> by (simp add: run_simps)
lemma nonzero_i64_min: \<open>run \<lbrakk>
  match NonZeroI64::new(-9223372036854775808_i64) {
    None \<Rightarrow> 0_i64,
    Some(nz) \<Rightarrow> nonzeroi64_get(nz)
  }
\<rbrakk> = Val (-9223372036854775808)\<close> by (simp add: run_simps)
lemma nonzero_i64_new_core_zero: \<open>nonzeroi64_new_core 0 = None\<close> by transfer simp



lemma simp_range_signed: \<open>range_into_list (make_range (-2 :: 8 sword) 1 False) = [-2, -1, 0]\<close> by (simp add: range_into_list_def upto.simps)
lemma simp_range_unsigned: \<open>range_into_list (make_range (254 :: 8 word) 255 True) = [254, 255]\<close> by (simp add: range_into_list_def upt_rec)



subsection\<open>Range patterns with a negative lower bound\<close>
lemma range_pat_incl_low: \<open>run \<lbrakk>
  let x = -5_i8;
  match Some(x) { Some(-5..=5) \<Rightarrow> 1_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma range_pat_incl_high: \<open>run \<lbrakk>
  let x = 5_i8;
  match Some(x) { Some(-5..=5) \<Rightarrow> 1_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma range_pat_incl_below: \<open>run \<lbrakk>
  let x = -6_i8;
  match Some(x) { Some(-5..=5) \<Rightarrow> 1_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma range_pat_incl_above: \<open>run \<lbrakk>
  let x = 6_i8;
  match Some(x) { Some(-5..=5) \<Rightarrow> 1_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma range_pat_incl_min: \<open>run \<lbrakk>
  let x = -128_i8;
  match Some(x) { Some(-5..=5) \<Rightarrow> 1_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma range_pat_incl_max: \<open>run \<lbrakk>
  let x = 127_i8;
  match Some(x) { Some(-5..=5) \<Rightarrow> 1_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma range_pat_excl_high: \<open>run \<lbrakk>
  let x = 5_i8;
  match Some(x) { Some(-5..5) \<Rightarrow> 1_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma range_pat_excl_inside: \<open>run \<lbrakk>
  let x = 4_i8;
  match Some(x) { Some(-5..5) \<Rightarrow> 1_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
subsection\<open>Range patterns with the bound -1\<close>
lemma range_pat_nested: \<open>run \<lbrakk>
  match Some(-3_i32) {
    Some(-5..=-1) \<Rightarrow> 1_i32,
    _ \<Rightarrow> 0_i32
  }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma range_pat_nested_miss: \<open>run \<lbrakk>
  match Some(0_i32) {
    Some(-5..=-1) \<Rightarrow> 1_i32,
    _ \<Rightarrow> 0_i32
  }
\<rbrakk> = Val 0\<close> by (simp add: run_simps)
lemma range_pat_guard: \<open>run \<lbrakk>
  let x = -3_i32;
  match Some(x) {
    Some(-5..=-1) if x == -2_i32 \<Rightarrow> 1_i32,
    Some(-5..=-1) if x == -3_i32 \<Rightarrow> 2_i32,
    _ \<Rightarrow> 0_i32
  }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
subsection\<open>Range patterns with the bounds -1, 0, 1\<close>
lemma range_pat_all_negative: \<open>run \<lbrakk>
  let x = -100_i8;
  match Some(x) { Some(-128..=-1) \<Rightarrow> 1_i8, Some(0) \<Rightarrow> 2_i8, Some(1..=127) \<Rightarrow> 3_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 1\<close> by (simp add: run_simps)
lemma range_pat_all_negative_zero: \<open>run \<lbrakk>
  let x = 0_i8;
  match Some(x) { Some(-128..=-1) \<Rightarrow> 1_i8, Some(0) \<Rightarrow> 2_i8, Some(1..=127) \<Rightarrow> 3_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 2\<close> by (simp add: run_simps)
lemma range_pat_all_negative_pos: \<open>run \<lbrakk>
  let x = 127_i8;
  match Some(x) { Some(-128..=-1) \<Rightarrow> 1_i8, Some(0) \<Rightarrow> 2_i8, Some(1..=127) \<Rightarrow> 3_i8, _ \<Rightarrow> 0_i8 }
\<rbrakk> = Val 3\<close> by (simp add: run_simps)
section\<open>Experiments on name resolution of \<^verbatim>\<open>cmp\<close> and \<^verbatim>\<open>Less\<close>\<close>

text\<open>In the lemmas above, \<^verbatim>\<open>x.cmp(y)\<close> resolved to \<^const>\<open>cmp\<close>. In the definition
\<^verbatim>\<open>i64_stdlib\<close> it stayed a free variable ("Extra variables on rhs: cmp"), so the definition
uses an antiquotation. The following isolate the forms.\<close>

definition cmp_in_def_call :: \<open>8 sword \<Rightarrow> (unit, StdLib_Ordering.ordering, StdLib_Ordering.ordering, unit, unit prompt, unit prompt_output) expression\<close> where
  \<open>cmp_in_def_call x \<equiv> \<lbrakk> cmp(x, x) \<rbrakk>\<close>
definition cmp_in_def_let :: \<open>8 sword \<Rightarrow> (unit, StdLib_Ordering.ordering, StdLib_Ordering.ordering, unit, unit prompt, unit prompt_output) expression\<close> where
  \<open>cmp_in_def_let x \<equiv> \<lbrakk> let y = x; y.cmp(y) \<rbrakk>\<close>
definition cmp_in_def_method :: \<open>8 sword \<Rightarrow> (unit, StdLib_Ordering.ordering, StdLib_Ordering.ordering, unit, unit prompt, unit prompt_output) expression\<close> where
  \<open>cmp_in_def_method x \<equiv> \<lbrakk> x.cmp(x) \<rbrakk>\<close>

lemma simp_cmp_signed: \<open>cmp_pure (-1 :: 8 sword) 0 = StdLib_Ordering.ordering.Less\<close> by (simp add: cmp_pure_def)
lemma simp_cmp_unsigned: \<open>cmp_pure (-1 :: 8 word) 0 = StdLib_Ordering.ordering.Greater\<close> by (simp add: cmp_pure_def)
lemma simp_cmp_unqualified: \<open>cmp_pure (-1 :: 8 sword) 0 = Less\<close> by (simp add: cmp_pure_def)

end
