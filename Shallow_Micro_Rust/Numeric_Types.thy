(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Numeric_Types
  imports Core_Expression Option_Type "Misc.Signedness"
begin
(*>*)

section\<open>Numeric types\<close>

consts
  urust_add :: \<open>('s, 'a, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'a, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'a, 'c, 'abort, 'i, 'o) expression\<close>

subsection\<open>Type definitions\<close>

text\<open>Casts follow Rust's \<^verbatim>\<open>as\<close>: the source is sign-extended if it is signed and
zero-extended otherwise, then truncated to the target width (see \<^const>\<open>word_rust_cast\<close>).\<close>

abbreviation ucastu8 :: \<open>('s, 'a::{len} word, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 8 word, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ucastu8 \<equiv> bind1 (literal \<circ> word_rust_cast)\<close>

abbreviation ucastu16 :: \<open>('s, 'a::{len} word, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 16 word, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ucastu16 \<equiv> bind1 (literal \<circ> word_rust_cast)\<close>

abbreviation ucastu32 :: \<open>('s, 'a::{len} word, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 32 word, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ucastu32 \<equiv> bind1 (literal \<circ> word_rust_cast)\<close>

abbreviation ucastu64 :: \<open>('s, 'a::{len} word, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 64 word, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ucastu64 \<equiv> bind1 (literal \<circ> word_rust_cast)\<close>

abbreviation ucasti8 :: \<open>('s, 'a::{len} word, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 8 sword, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ucasti8 \<equiv> bind1 (literal \<circ> word_rust_cast)\<close>

abbreviation ucasti16 :: \<open>('s, 'a::{len} word, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 16 sword, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ucasti16 \<equiv> bind1 (literal \<circ> word_rust_cast)\<close>

abbreviation ucasti32 :: \<open>('s, 'a::{len} word, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 32 sword, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ucasti32 \<equiv> bind1 (literal \<circ> word_rust_cast)\<close>

abbreviation ucasti64 :: \<open>('s, 'a::{len} word, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 64 sword, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ucasti64 \<equiv> bind1 (literal \<circ> word_rust_cast)\<close>

abbreviation ascribeu8 :: \<open>8 word \<Rightarrow> ('s, 8 word, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ascribeu8 \<equiv> literal\<close>

abbreviation ascribeu16 :: \<open>16 word \<Rightarrow> ('s, 16 word, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ascribeu16 \<equiv> literal\<close>

abbreviation ascribeu32 :: \<open>32 word \<Rightarrow> ('s, 32 word, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ascribeu32 \<equiv> literal\<close>

abbreviation ascribeu64 :: \<open>64 word \<Rightarrow> ('s, 64 word, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ascribeu64 \<equiv> literal\<close>

abbreviation ascribei8 :: \<open>8 sword \<Rightarrow> ('s, 8 sword, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ascribei8 \<equiv> literal\<close>

abbreviation ascribei16 :: \<open>16 sword \<Rightarrow> ('s, 16 sword, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ascribei16 \<equiv> literal\<close>

abbreviation ascribei32 :: \<open>32 sword \<Rightarrow> ('s, 32 sword, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ascribei32 \<equiv> literal\<close>

abbreviation ascribei64 :: \<open>64 sword \<Rightarrow> ('s, 64 sword, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>ascribei64 \<equiv> literal\<close>

subsection\<open>Arithmetic\<close>

text\<open>Here, we implement non-overflowing word arithmetic. First, the pure definitions:\<close>

definition word_op_no_wrap_pure :: \<open>(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> 'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word option\<close> where
  \<open>word_op_no_wrap_pure op a b \<equiv>
     let op_nat = op (unat a) (unat b) in
       if op_nat < 2^LENGTH('l) then
         Some (word_of_nat op_nat)
       else
         None\<close>

text\<open>For signed words, the operation is performed on the signed values and must stay within the
signed range of the type.\<close>

definition sword_op_no_wrap_pure :: \<open>(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> 'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word option\<close> where
  \<open>sword_op_no_wrap_pure op a b \<equiv>
     let op_int = op (sint a) (sint b) in
       if - (2 ^ (LENGTH('l) - Suc 0)) \<le> op_int \<and> op_int < 2 ^ (LENGTH('l) - Suc 0) then
         Some (word_of_int op_int)
       else
         None\<close>

definition word_minus_no_wrap_pure :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word option\<close> where
  \<open>word_minus_no_wrap_pure a b \<equiv>
     if is_signed TYPE('l) then
       sword_op_no_wrap_pure (-) a b
     else if (b \<le> a) then
       Some (a - b)
     else
       None\<close>

abbreviation word_add_no_wrap_pure :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('l word) option\<close> where
  \<open>word_add_no_wrap_pure a b \<equiv>
     if is_signed TYPE('l) then sword_op_no_wrap_pure (+) a b
     else word_op_no_wrap_pure ((+) :: nat \<Rightarrow> nat \<Rightarrow> nat) a b\<close>

abbreviation word_mul_no_wrap_pure :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('l word) option\<close> where
  \<open>word_mul_no_wrap_pure a b \<equiv>
     if is_signed TYPE('l) then sword_op_no_wrap_pure (*) a b
     else word_op_no_wrap_pure ((*) :: nat \<Rightarrow> nat \<Rightarrow> nat) a b\<close>

text\<open>We lift this to Micro Rust expressions by panicking in case of an arithmetic overflow.\<close>

definition word_add_no_wrap_as_urust :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word option, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_add_no_wrap_as_urust \<equiv> lift_exp2 word_add_no_wrap_pure\<close>

definition word_mul_no_wrap_as_urust :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word option, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_mul_no_wrap_as_urust \<equiv> lift_exp2 word_mul_no_wrap_pure\<close>

definition word_minus_no_wrap_as_urust :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word option, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_minus_no_wrap_as_urust \<equiv> lift_exp2 word_minus_no_wrap_pure\<close>

definition overflow_err_msg :: String.literal where
  \<open>overflow_err_msg \<equiv> String.implode ''arithmetic overflow''\<close>

definition word_add_no_wrap_core :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_add_no_wrap_core a b \<equiv>
     bind (word_add_no_wrap_as_urust a b) (option_unwrap_expr overflow_err_msg)\<close>

definition word_mul_no_wrap_core :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_mul_no_wrap_core a b \<equiv>
     bind (word_mul_no_wrap_as_urust a b) (option_unwrap_expr overflow_err_msg)\<close>

definition word_minus_no_wrap_core :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_minus_no_wrap_core a b \<equiv>
     bind (word_minus_no_wrap_as_urust a b) (option_unwrap_expr overflow_err_msg)\<close>

text\<open>Signed division truncates towards zero, and the remainder has the sign of the dividend
(\<^const>\<open>signed_divide\<close>, \<^const>\<open>signed_modulo\<close>). Dividing the minimum value by \<open>-1\<close>
overflows, and so does the corresponding remainder.\<close>

definition word_udiv_core :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_udiv_core a b \<equiv>
     if is_signed TYPE('l) then
       (if b = 0 then panic (String.implode ''division by zero'')
        else if sint a = - (2 ^ (LENGTH('l) - Suc 0)) \<and> b = -1 then panic overflow_err_msg
        else literal (a sdiv b))
     else if b = 0 then panic (String.implode ''division by zero'') else literal (a div b)\<close>

definition word_umod_core :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_umod_core a b \<equiv>
     if is_signed TYPE('l) then
       (if b = 0 then panic (String.implode ''division by zero'')
        else if sint a = - (2 ^ (LENGTH('l) - Suc 0)) \<and> b = -1 then panic overflow_err_msg
        else literal (a smod b))
     else if b = 0 then panic (String.implode ''division by zero'') else literal (a mod b)\<close>

definition word_add_no_wrap :: \<open>('s, 'l::{len} word, 'r, 'abort, 'i, 'o) urust_binop\<close> where
  \<open>word_add_no_wrap \<equiv> bind2 word_add_no_wrap_core\<close>
adhoc_overloading urust_add \<rightleftharpoons> word_add_no_wrap

definition word_minus_no_wrap :: \<open>('s, 'l::{len} word, 'r, 'abort, 'i, 'o) urust_binop\<close> where
  \<open>word_minus_no_wrap \<equiv> bind2 word_minus_no_wrap_core\<close>

definition word_mul_no_wrap :: \<open>('s, 'l::{len} word, 'r, 'abort, 'i, 'o) urust_binop\<close> where
  \<open>word_mul_no_wrap \<equiv> bind2 word_mul_no_wrap_core\<close>

text\<open>Unary negation is subtraction from zero. For signed words it overflows exactly on the
minimum value.\<close>

definition word_uminus :: \<open>('s, 'l::{len} word, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_uminus e \<equiv> word_minus_no_wrap (literal 0) e\<close>

definition word_udiv :: \<open>('s, 'l::{len} word, 'r, 'abort, 'i, 'o) urust_binop\<close> where
  \<open>word_udiv \<equiv> bind2 word_udiv_core\<close>

definition word_umod :: \<open>('s, 'l::{len} word, 'r, 'abort, 'i, 'o) urust_binop\<close> where
  \<open>word_umod \<equiv> bind2 word_umod_core\<close>

subsection\<open>Bitwise operations\<close>

context
begin

unbundle bit_operations_syntax

\<comment>\<open>From the Rust doc:
  \<^verbatim>\<open>Using << or >> where the right-hand argument is greater than or equal to
    the number of bits in the type of the left-hand argument, or is negative.\<close>\<close>
definition word_shift_left_pure :: \<open>'l0::{len} word \<Rightarrow> 'l1::len word \<Rightarrow> 'l0 word option\<close> where
  \<open>word_shift_left_pure u v \<equiv>
     if unat v \<ge> LENGTH('l0) then
        None
     else
        Some (push_bit (unat v) u)\<close>

definition word_shift_right_pure :: \<open>'l0::{len} word \<Rightarrow> 'l1::len word \<Rightarrow> 'l0 word option\<close> where
  \<open>word_shift_right_pure u v \<equiv>
     if is_signed TYPE('l0) then
       (if unat v \<ge> LENGTH('l0) then
          None
        else
          Some (signed_drop_bit (unat v) u))
     else if unat v \<ge> LENGTH('l0) then
        None
     else
        Some (drop_bit (unat v) u)\<close>

definition word_shift_left_as_urust :: \<open>'l0::{len} word \<Rightarrow> 'l1::{len} word \<Rightarrow> ('s, 'l0 word option, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_shift_left_as_urust \<equiv> lift_exp2 word_shift_left_pure\<close>

definition word_shift_right_as_urust :: \<open>'l0::{len} word \<Rightarrow> 'l1::{len} word \<Rightarrow> ('s, 'l0 word option, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_shift_right_as_urust \<equiv> lift_exp2 word_shift_right_pure\<close>

definition word_shift_left_core :: \<open>'l0::{len} word \<Rightarrow> 'l1::{len} word \<Rightarrow> ('s, 'l0 word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_shift_left_core a b \<equiv> bind (word_shift_left_as_urust a b) (option_unwrap_expr overflow_err_msg)\<close>

definition word_shift_right_core :: \<open>'l0::{len} word \<Rightarrow> 'l1::{len} word \<Rightarrow> ('s, 'l0 word, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>word_shift_right_core a b \<equiv> bind (word_shift_right_as_urust a b) (option_unwrap_expr overflow_err_msg)\<close>

definition word_shift_left :: \<open>('s, 'l0::len word, 'l1::len word, 'l0 word, 'r, 'abort, 'i, 'o) urust_binop3\<close> where
  \<open>word_shift_left a b \<equiv> bind2 word_shift_left_core a b\<close>

definition word_shift_right :: \<open>('s, 'l0::{len} word, 'l1::{len} word, 'l0 word, 'r, 'abort, 'i, 'o) urust_binop3\<close> where
  \<open>word_shift_right a b \<equiv> bind2 word_shift_right_core a b\<close>

text\<open>To avoid explicit type annotations in numeral expressions like \<^verbatim>\<open>foo << 42\<close>, we fix the type of
the shift parameter to be \<^verbatim>\<open>64 word\<close> in \<^verbatim>\<open>\<mu>Rust\<close>.\<close>
definition word_shift_left_shift64 :: \<open>('s, 'l0::{len} word, 64 word, 'l0 word, 'r, 'abort, 'i, 'o) urust_binop3\<close> where
  \<open>word_shift_left_shift64 \<equiv> word_shift_left\<close>

definition word_shift_right_shift64 :: \<open>('s, 'l0::len word, 64 word, 'l0 word, 'r, 'abort, 'i, 'o) urust_binop3\<close> where
  \<open>word_shift_right_shift64 \<equiv> word_shift_right\<close>

definition word_bitwise_xor_pure :: \<open>'l::{len} word \<Rightarrow> 'l word  \<Rightarrow> 'l word\<close> where
  \<open>word_bitwise_xor_pure w c \<equiv> w XOR c\<close>

definition word_bitwise_xor :: \<open>('s, 'l::{len} word, 'r, 'abort, 'i, 'o) urust_binop\<close> where
  \<open>word_bitwise_xor \<equiv> bindlift2 word_bitwise_xor_pure\<close>

definition word_bitwise_and_pure :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word\<close> where
    \<open>word_bitwise_and_pure w c \<equiv> w AND c\<close>

definition word_bitwise_and :: \<open>('s, 'l::{len} word, 'r, 'abort, 'i, 'o) urust_binop\<close> where
    \<open>word_bitwise_and \<equiv> bindlift2 word_bitwise_and_pure\<close>

definition word_bitwise_or_pure :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word\<close> where
    \<open>word_bitwise_or_pure w c \<equiv> w OR c\<close>

definition word_bitwise_or :: \<open>('s, 'l::{len} word, 'r, 'abort, 'i, 'o) urust_binop\<close> where
    \<open>word_bitwise_or \<equiv> bindlift2 word_bitwise_or_pure\<close>

definition word_bitwise_not_pure :: \<open>'l::{len} word \<Rightarrow> 'l word\<close> where
    \<open>word_bitwise_not_pure w \<equiv> NOT w\<close>

definition word_bitwise_not :: \<open>('s, 'l::{len} word, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'l word, 'r, 'abort, 'i, 'o) expression\<close> where
    \<open>word_bitwise_not \<equiv> bindlift1 word_bitwise_not_pure\<close>

end

subsection\<open>Widening arithmetic casts\<close>

text\<open>We define various widening arithmetic casts embedding smaller word types into larger ones.\<close>

subsection\<open>The \<^verbatim>\<open>64 word\<close> type\<close>

definition u64_from_u32 :: \<open>32 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close> ("u64::from\<^sub>u\<^sub>3\<^sub>2") where
  [micro_rust_simps]: \<open>u64_from_u32 \<equiv> lift_fun1 ucast\<close>

definition u64_from_u16 :: \<open>16 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close> ("u64::from\<^sub>u\<^sub>1\<^sub>6") where
  [micro_rust_simps]: \<open>u64_from_u16 \<equiv> lift_fun1 ucast\<close>

definition u64_from_u8 :: \<open>8 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close> ("u64::from\<^sub>u\<^sub>8") where
  [micro_rust_simps]: \<open>u64_from_u8 \<equiv> lift_fun1 ucast\<close>

definition i64_from_i32 :: \<open>32 sword \<Rightarrow> ('s, 64 sword, 'abort, 'i, 'o) function_body\<close> ("i64::from\<^sub>i\<^sub>3\<^sub>2") where
  [micro_rust_simps]: \<open>i64_from_i32 \<equiv> lift_fun1 scast\<close>

definition i64_from_i16 :: \<open>16 sword \<Rightarrow> ('s, 64 sword, 'abort, 'i, 'o) function_body\<close> ("i64::from\<^sub>i\<^sub>1\<^sub>6") where
  [micro_rust_simps]: \<open>i64_from_i16 \<equiv> lift_fun1 scast\<close>

definition i64_from_i8 :: \<open>8 sword \<Rightarrow> ('s, 64 sword, 'abort, 'i, 'o) function_body\<close> ("i64::from\<^sub>i\<^sub>8") where
  [micro_rust_simps]: \<open>i64_from_i8 \<equiv> lift_fun1 scast\<close>

subsection\<open>Narrowing arithmetic casts\<close>

text\<open>Next, we define various narrowing casts from larger into smaller word types, failing gracefully in case
the word to be converted is not expressible in the target type.\<close>

definition word_try_from_pure :: \<open>'l0::{len} word \<Rightarrow> 'l1::{len} word option\<close> where
  \<open>word_try_from_pure a \<equiv>
     if is_signed TYPE('l0) \<or> is_signed TYPE('l1) then
       (let v = if is_signed TYPE('l0) then sint a else uint a in
        if (if is_signed TYPE('l1) then
              - (2 ^ (LENGTH('l1) - Suc 0)) \<le> v \<and> v < 2 ^ (LENGTH('l1) - Suc 0)
            else 0 \<le> v \<and> v < 2 ^ LENGTH('l1)) then
          Some (word_of_int v)
        else
          None)
     else if unat a < 2^LENGTH('l1) then
       Some (ucast a)
     else
       None\<close>

definition word_try_from_fun :: \<open>'l0::{len} word \<Rightarrow> ('s, 'l1::{len} word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>word_try_from_fun \<equiv> lift_fun1 word_try_from_pure\<close>

text\<open>Give names familiar from Rust to various specializations of this function.\<close>

abbreviation usize_try_from_u64_pure :: \<open>64 word \<Rightarrow> 64 word option\<close> ("usize::try'_from\<^sub>u\<^sub>6\<^sub>4") where
  \<open>usize_try_from_u64_pure \<equiv> word_try_from_pure\<close>

abbreviation u32_try_from_u64_pure :: \<open>64 word \<Rightarrow> 32 word option\<close> ("u32::try'_from\<^sub>u\<^sub>6\<^sub>4") where
  \<open>u32_try_from_u64_pure \<equiv> word_try_from_pure\<close>

abbreviation u16_try_from_u64_pure :: \<open>64 word \<Rightarrow> 16 word option\<close> ("u16::try'_from\<^sub>u\<^sub>6\<^sub>4") where
  \<open>u16_try_from_u64_pure \<equiv> word_try_from_pure\<close>

abbreviation u8_try_from_u64_pure :: \<open>64 word \<Rightarrow> 8 word option\<close> ("u8::try'_from\<^sub>u\<^sub>6\<^sub>4") where
  \<open>u8_try_from_u64_pure \<equiv> word_try_from_pure\<close>

abbreviation u32_try_from_usize_pure :: \<open>64 word \<Rightarrow> 32 word option\<close> ("u32::try'_from\<^sub>u\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>u32_try_from_usize_pure \<equiv> word_try_from_pure\<close>

abbreviation u16_try_from_usize_pure :: \<open>64 word \<Rightarrow> 16 word option\<close> ("u16::try'_from\<^sub>u\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>u16_try_from_usize_pure \<equiv> word_try_from_pure\<close>

abbreviation u8_try_from_usize_pure :: \<open>64 word \<Rightarrow> 8 word option\<close> ("u8::try'_from\<^sub>u\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>u8_try_from_usize_pure \<equiv> word_try_from_pure\<close>

abbreviation u16_try_from_u32_pure :: \<open>32 word \<Rightarrow> 16 word option\<close> ("u16::try'_from\<^sub>u\<^sub>3\<^sub>2") where
  \<open>u16_try_from_u32_pure \<equiv> word_try_from_pure\<close>

abbreviation u8_try_from_u32_pure :: \<open>32 word \<Rightarrow> 8 word option\<close> ("u8::try'_from\<^sub>u\<^sub>3\<^sub>2") where
  \<open>u8_try_from_u32_pure \<equiv> word_try_from_pure\<close>

abbreviation u8_try_from_u16_pure :: \<open>16 word \<Rightarrow> 8 word option\<close> ("u16::try'_from\<^sub>u\<^sub>1\<^sub>6") where
  \<open>u8_try_from_u16_pure \<equiv> word_try_from_pure\<close>

abbreviation usize_try_from_u64 :: \<open>64 word \<Rightarrow> ('s, 64 word option, 'abort, 'i, 'o) function_body\<close> ("usize::try'_from\<^sub>u\<^sub>6\<^sub>4") where
  \<open>usize_try_from_u64 \<equiv> word_try_from_fun\<close>

abbreviation u32_try_from_u64 :: \<open>64 word \<Rightarrow> ('s, 32 word option, 'abort, 'i, 'o) function_body\<close> ("u32::try'_from\<^sub>u\<^sub>6\<^sub>4") where
  \<open>u32_try_from_u64 \<equiv> word_try_from_fun\<close>

abbreviation u16_try_from_u64 :: \<open>64 word \<Rightarrow> ('s, 16 word option, 'abort, 'i, 'o) function_body\<close> ("u16::try'_from\<^sub>u\<^sub>6\<^sub>4") where
  \<open>u16_try_from_u64 \<equiv> word_try_from_fun\<close>

abbreviation u8_try_from_u64 :: \<open>64 word \<Rightarrow> ('s, 8 word option, 'abort, 'i, 'o) function_body\<close> ("u8::try'_from\<^sub>u\<^sub>6\<^sub>4") where
  \<open>u8_try_from_u64 \<equiv> word_try_from_fun\<close>

abbreviation u32_try_from_usize :: \<open>64 word \<Rightarrow> ('s, 32 word option, 'abort, 'i, 'o) function_body\<close> ("u32::try'_from\<^sub>u\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>u32_try_from_usize \<equiv> word_try_from_fun\<close>

abbreviation u16_try_from_usize :: \<open>64 word \<Rightarrow> ('s, 16 word option, 'abort, 'i, 'o) function_body\<close> ("u16::try'_from\<^sub>u\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>u16_try_from_usize \<equiv> word_try_from_fun\<close>

abbreviation u8_try_from_usize :: \<open>64 word \<Rightarrow> ('s, 8 word option, 'abort, 'i, 'o) function_body\<close> ("u8::try'_from\<^sub>u\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>u8_try_from_usize \<equiv> word_try_from_fun\<close>

abbreviation u16_try_from_u32 :: \<open>32 word \<Rightarrow> ('s, 16 word option, 'abort, 'i, 'o) function_body\<close> ("u16::try'_from\<^sub>u\<^sub>3\<^sub>2") where
  \<open>u16_try_from_u32 \<equiv> word_try_from_fun\<close>

abbreviation u8_try_from_u32 :: \<open>32 word \<Rightarrow> ('s, 8 word option, 'abort, 'i, 'o) function_body\<close> ("u8::try'_from\<^sub>u\<^sub>3\<^sub>2") where
  \<open>u8_try_from_u32 \<equiv> word_try_from_fun\<close>

abbreviation u8_try_from_u16 :: \<open>16 word \<Rightarrow> ('s, 8 word option, 'abort, 'i, 'o) function_body\<close> ("u16::try'_from\<^sub>u\<^sub>1\<^sub>6") where
  \<open>u8_try_from_u16 \<equiv> word_try_from_fun\<close>

abbreviation isize_try_from_i64_pure :: \<open>64 sword \<Rightarrow> 64 sword option\<close> ("isize::try'_from\<^sub>i\<^sub>6\<^sub>4") where
  \<open>isize_try_from_i64_pure \<equiv> word_try_from_pure\<close>

abbreviation i32_try_from_i64_pure :: \<open>64 sword \<Rightarrow> 32 sword option\<close> ("i32::try'_from\<^sub>i\<^sub>6\<^sub>4") where
  \<open>i32_try_from_i64_pure \<equiv> word_try_from_pure\<close>

abbreviation i16_try_from_i64_pure :: \<open>64 sword \<Rightarrow> 16 sword option\<close> ("i16::try'_from\<^sub>i\<^sub>6\<^sub>4") where
  \<open>i16_try_from_i64_pure \<equiv> word_try_from_pure\<close>

abbreviation i8_try_from_i64_pure :: \<open>64 sword \<Rightarrow> 8 sword option\<close> ("i8::try'_from\<^sub>i\<^sub>6\<^sub>4") where
  \<open>i8_try_from_i64_pure \<equiv> word_try_from_pure\<close>

abbreviation i32_try_from_isize_pure :: \<open>64 sword \<Rightarrow> 32 sword option\<close> ("i32::try'_from\<^sub>i\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>i32_try_from_isize_pure \<equiv> word_try_from_pure\<close>

abbreviation i16_try_from_isize_pure :: \<open>64 sword \<Rightarrow> 16 sword option\<close> ("i16::try'_from\<^sub>i\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>i16_try_from_isize_pure \<equiv> word_try_from_pure\<close>

abbreviation i8_try_from_isize_pure :: \<open>64 sword \<Rightarrow> 8 sword option\<close> ("i8::try'_from\<^sub>i\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>i8_try_from_isize_pure \<equiv> word_try_from_pure\<close>

abbreviation i16_try_from_i32_pure :: \<open>32 sword \<Rightarrow> 16 sword option\<close> ("i16::try'_from\<^sub>i\<^sub>3\<^sub>2") where
  \<open>i16_try_from_i32_pure \<equiv> word_try_from_pure\<close>

abbreviation i8_try_from_i32_pure :: \<open>32 sword \<Rightarrow> 8 sword option\<close> ("i8::try'_from\<^sub>i\<^sub>3\<^sub>2") where
  \<open>i8_try_from_i32_pure \<equiv> word_try_from_pure\<close>

abbreviation i8_try_from_i16_pure :: \<open>16 sword \<Rightarrow> 8 sword option\<close> ("i8::try'_from\<^sub>i\<^sub>1\<^sub>6") where
  \<open>i8_try_from_i16_pure \<equiv> word_try_from_pure\<close>

abbreviation isize_try_from_i64 :: \<open>64 sword \<Rightarrow> ('s, 64 sword option, 'abort, 'i, 'o) function_body\<close> ("isize::try'_from\<^sub>i\<^sub>6\<^sub>4") where
  \<open>isize_try_from_i64 \<equiv> word_try_from_fun\<close>

abbreviation i32_try_from_i64 :: \<open>64 sword \<Rightarrow> ('s, 32 sword option, 'abort, 'i, 'o) function_body\<close> ("i32::try'_from\<^sub>i\<^sub>6\<^sub>4") where
  \<open>i32_try_from_i64 \<equiv> word_try_from_fun\<close>

abbreviation i16_try_from_i64 :: \<open>64 sword \<Rightarrow> ('s, 16 sword option, 'abort, 'i, 'o) function_body\<close> ("i16::try'_from\<^sub>i\<^sub>6\<^sub>4") where
  \<open>i16_try_from_i64 \<equiv> word_try_from_fun\<close>

abbreviation i8_try_from_i64 :: \<open>64 sword \<Rightarrow> ('s, 8 sword option, 'abort, 'i, 'o) function_body\<close> ("i8::try'_from\<^sub>i\<^sub>6\<^sub>4") where
  \<open>i8_try_from_i64 \<equiv> word_try_from_fun\<close>

abbreviation i32_try_from_isize :: \<open>64 sword \<Rightarrow> ('s, 32 sword option, 'abort, 'i, 'o) function_body\<close> ("i32::try'_from\<^sub>i\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>i32_try_from_isize \<equiv> word_try_from_fun\<close>

abbreviation i16_try_from_isize :: \<open>64 sword \<Rightarrow> ('s, 16 sword option, 'abort, 'i, 'o) function_body\<close> ("i16::try'_from\<^sub>i\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>i16_try_from_isize \<equiv> word_try_from_fun\<close>

abbreviation i8_try_from_isize :: \<open>64 sword \<Rightarrow> ('s, 8 sword option, 'abort, 'i, 'o) function_body\<close> ("i8::try'_from\<^sub>i\<^sub>s\<^sub>i\<^sub>z\<^sub>e") where
  \<open>i8_try_from_isize \<equiv> word_try_from_fun\<close>

abbreviation i16_try_from_i32 :: \<open>32 sword \<Rightarrow> ('s, 16 sword option, 'abort, 'i, 'o) function_body\<close> ("i16::try'_from\<^sub>i\<^sub>3\<^sub>2") where
  \<open>i16_try_from_i32 \<equiv> word_try_from_fun\<close>

abbreviation i8_try_from_i32 :: \<open>32 sword \<Rightarrow> ('s, 8 sword option, 'abort, 'i, 'o) function_body\<close> ("i8::try'_from\<^sub>i\<^sub>3\<^sub>2") where
  \<open>i8_try_from_i32 \<equiv> word_try_from_fun\<close>

abbreviation i8_try_from_i16 :: \<open>16 sword \<Rightarrow> ('s, 8 sword option, 'abort, 'i, 'o) function_body\<close> ("i8::try'_from\<^sub>i\<^sub>1\<^sub>6") where
  \<open>i8_try_from_i16 \<equiv> word_try_from_fun\<close>

subsection\<open>Signedness in the \<mu>Rust simplifier\<close>

text\<open>The \<mu>Rust simplification rules for operations on words carry a premise on the signedness of
the length type. The following rules discharge it for concrete lengths and reduce the comparisons
and casts accordingly.\<close>

text\<open>Crush applies the \<mu>Rust simplification rules on their own, so the rules that finish
evaluating a premise like \<^term>\<open>\<not> is_signed TYPE(64)\<close> are added as well.\<close>

declare not_False_eq_True[micro_rust_simps] not_True_eq_False[micro_rust_simps]
  if_True[micro_rust_simps] if_False[micro_rust_simps]

text\<open>Unary negation is evaluated as subtraction from zero.\<close>

declare word_uminus_def[micro_rust_simps]

declare is_signed_simps[micro_rust_simps]
  word_rust_lt_unsigned[micro_rust_simps] word_rust_lt_signed[micro_rust_simps]
  word_rust_le_unsigned[micro_rust_simps] word_rust_le_signed[micro_rust_simps]
  word_rust_cast_unsigned[micro_rust_simps] word_rust_cast_signed[micro_rust_simps]
  word_rust_cast_unsigned_comp[micro_rust_simps] word_rust_cast_signed_comp[micro_rust_simps]

subsection\<open>Code generation\<close>

text\<open>The operations branch on \<^const>\<open>is_signed\<close>, which has no code equations. They are unfolded
into their uses at concrete word lengths (see \<^verbatim>\<open>Signedness\<close>).\<close>

declare word_add_no_wrap_def[abs_def, code_unfold] word_add_no_wrap_core_def[abs_def, code_unfold]
  word_add_no_wrap_as_urust_def[abs_def, code_unfold]
  word_mul_no_wrap_def[abs_def, code_unfold] word_mul_no_wrap_core_def[abs_def, code_unfold]
  word_mul_no_wrap_as_urust_def[abs_def, code_unfold]
  word_minus_no_wrap_def[abs_def, code_unfold] word_minus_no_wrap_core_def[abs_def, code_unfold]
  word_minus_no_wrap_as_urust_def[abs_def, code_unfold] word_minus_no_wrap_pure_def[abs_def, code_unfold]
  word_udiv_def[abs_def, code_unfold] word_udiv_core_def[abs_def, code_unfold]
  word_umod_def[abs_def, code_unfold] word_umod_core_def[abs_def, code_unfold]
  word_uminus_def[abs_def, code_unfold]
  word_shift_right_def[abs_def, code_unfold] word_shift_right_shift64_def[abs_def, code_unfold]
  word_shift_right_core_def[abs_def, code_unfold] word_shift_right_as_urust_def[abs_def, code_unfold]
  word_shift_right_pure_def[abs_def, code_unfold]
  word_try_from_pure_def[abs_def, code_unfold] word_try_from_fun_def[abs_def, code_unfold]

(*<*)
end
(*>*)