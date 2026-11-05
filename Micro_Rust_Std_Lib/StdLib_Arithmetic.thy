(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Arithmetic
  imports Crush.Crush StdLib_References
begin
(*>*)

subsection\<open>Arithmetic\<close>

text\<open>Each operation is defined for unsigned and signed words. For signed words
(\<^term>\<open>is_signed TYPE('l)\<close>), the operation follows Rust's semantics on the signed values
\<^const>\<open>sint\<close>, whose range is \<open>[-2^(LENGTH('l) - 1), 2^(LENGTH('l) - 1))\<close>.\<close>

definition overflowing_mul :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('machine, 'l word \<times> bool \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>overflowing_mul x y \<equiv> FunctionBody(literal (
     if is_signed TYPE('l) then
       (x * y, sint x * sint y < - (2 ^ (LENGTH('l) - Suc 0)) \<or> 2 ^ (LENGTH('l) - Suc 0) \<le> sint x * sint y, TNil)
     else (x * y, unat x * unat y \<ge> 2^LENGTH('l), TNil)))\<close>

definition overflowing_add :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
    ('machine, 'l word \<times> bool \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>overflowing_add x y \<equiv> FunctionBody (literal (
     if is_signed TYPE('l) then
       (x + y, sint x + sint y < - (2 ^ (LENGTH('l) - Suc 0)) \<or> 2 ^ (LENGTH('l) - Suc 0) \<le> sint x + sint y, TNil)
     else (x + y, unat x + unat y \<ge> 2^LENGTH('l), TNil)))\<close>

text\<open>In Rust, \<^verbatim>\<open>wrapping_add_unsigned\<close> exists only on signed integer types: it adds an
unsigned integer of the same width to a signed integer, wrapping around on overflow.\<close>

definition wrapping_add_unsigned :: \<open>'l::{len} signed word \<Rightarrow> 'l word \<Rightarrow>
    ('machine, 'l signed word, 'abort, 'i, 'o) function_body\<close> where
  \<open>wrapping_add_unsigned \<equiv> \<lambda>self rhs. FunctionBody (literal (self + ucast rhs))\<close>

text\<open>For signed words, saturating subtraction clamps the result to the minimum and maximum value
of the type.\<close>

definition word_sub_saturating_core :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> 'l word\<close> where
  \<open>word_sub_saturating_core e f \<equiv>
     if is_signed TYPE('l) then
       (if sint e - sint f < - (2 ^ (LENGTH('l) - Suc 0)) then word_of_int (- (2 ^ (LENGTH('l) - Suc 0)))
        else if 2 ^ (LENGTH('l) - Suc 0) \<le> sint e - sint f then word_of_int (2 ^ (LENGTH('l) - Suc 0) - 1)
        else word_of_int (sint e - sint f))
     else if e < f then 0 else e - f\<close>

definition saturating_sub :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>saturating_sub e f \<equiv> FunctionBody (literal (word_sub_saturating_core e f))\<close>

definition checked_mul_core :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word option\<close> where
  \<open>checked_mul_core w v \<equiv>
     if is_signed TYPE('a) then
       (if - (2 ^ (LENGTH('a) - Suc 0)) \<le> sint w * sint v \<and> sint w * sint v < 2 ^ (LENGTH('a) - Suc 0) then Some (w * v) else None)
     else if unat w * unat v \<ge> 2^LENGTH('a) then None else Some (w * v)\<close>

definition checked_add_core :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word option\<close> where
  \<open>checked_add_core w v \<equiv>
     if is_signed TYPE('a) then
       (if - (2 ^ (LENGTH('a) - Suc 0)) \<le> sint w + sint v \<and> sint w + sint v < 2 ^ (LENGTH('a) - Suc 0) then Some (w + v) else None)
     else if unat w + unat v \<ge> 2^LENGTH('a) then None else Some (w + v)\<close>

definition checked_mul :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('s, 'a word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>checked_mul w v \<equiv> FunctionBody (literal (checked_mul_core w v))\<close>

definition checked_add :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('s, 'a word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>checked_add w v \<equiv> FunctionBody (literal (checked_add_core w v))\<close>

text\<open>For signed words, \<^verbatim>\<open>div_ceil\<close> rounds the quotient towards positive infinity. The
ceiling of \<open>a / b\<close> is \<open>- ((- a) div b)\<close>, because \<^const>\<open>divide\<close> on \<^typ>\<open>int\<close> rounds
towards negative infinity. As for signed division, dividing by zero panics, and dividing the minimum
value by \<open>-1\<close> overflows and panics.\<close>

definition div_ceil_pure :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close> where
  \<open>div_ceil_pure x y \<equiv>
     if is_signed TYPE('a) then
       word_of_int (- ((- sint x) div sint y))
     else (x + y - 1) div y\<close>

definition div_ceil :: \<open>'a::{len} word \<Rightarrow> 'a word \<Rightarrow> ('machine, 'a word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>div_ceil x y \<equiv> FunctionBody (
     if is_signed TYPE('a) then
       (if y = 0 then panic (String.implode ''division by zero'')
        else if sint x = - (2 ^ (LENGTH('a) - Suc 0)) \<and> y = -1 then panic overflow_err_msg
        else literal (div_ceil_pure x y))
     else literal (div_ceil_pure x y))\<close>

\<comment> \<open>Contracts and verifications\<close>

definition overflowing_mul_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word \<times> bool \<times> tnil, 'b) function_contract\<close> where
  [crush_contracts]: \<open>overflowing_mul_contract x y \<equiv>
    let pre = emp in \<comment> \<open>Any inputs are acceptable, and no resource is needed\<close>
    let post = \<lambda>ret. \<langle>ret = (
      if is_signed TYPE('l) then
        (x * y, sint x * sint y < - (2 ^ (LENGTH('l) - Suc 0)) \<or> 2 ^ (LENGTH('l) - Suc 0) \<le> sint x * sint y, TNil)
      else (x * y, unat x * unat y \<ge> 2^LENGTH('l), TNil))\<rangle> in
      make_function_contract pre post\<close>

lemma overflowing_mul_spec [crush_specs]:
  shows \<open>\<Gamma> ; overflowing_mul x y \<Turnstile>\<^sub>F overflowing_mul_contract x y\<close>
by (crush_boot f: overflowing_mul_def contract: overflowing_mul_contract_def) crush_base

definition overflowing_add_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word \<times> bool \<times> tnil, 'b) function_contract\<close>where
  [crush_contracts]: \<open>overflowing_add_contract x y \<equiv>
    let pre = emp in
    let post = \<lambda>ret. \<langle>ret = (
      if is_signed TYPE('l) then
        (x + y, sint x + sint y < - (2 ^ (LENGTH('l) - Suc 0)) \<or> 2 ^ (LENGTH('l) - Suc 0) \<le> sint x + sint y, TNil)
      else (x + y, unat x + unat y \<ge> 2^LENGTH('l), TNil))\<rangle> in
      make_function_contract pre post\<close>

lemma overflowing_add_spec [crush_specs]:
  shows \<open>\<Gamma> ; overflowing_add x y \<Turnstile>\<^sub>F overflowing_add_contract x y\<close>
by (crush_boot f: overflowing_add_def contract: overflowing_add_contract_def) crush_base

definition wrapping_add_unsigned_contract :: \<open>'l::{len} signed word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l signed word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>wrapping_add_unsigned_contract x y \<equiv>
    let pre = emp in
    let post = \<lambda>ret. \<langle>ret = x + ucast y\<rangle> in
      make_function_contract pre post\<close>

lemma wrapping_add_unsigned_spec [crush_specs]:
  shows \<open>\<Gamma> ; wrapping_add_unsigned x y \<Turnstile>\<^sub>F wrapping_add_unsigned_contract x y\<close>
by (crush_boot f: wrapping_add_unsigned_def contract: wrapping_add_unsigned_contract_def) crush_base

definition saturating_sub_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow>
      ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>saturating_sub_contract x y \<equiv>
    let pre = emp in
    let post = \<lambda>ret. \<langle>ret = (
      if is_signed TYPE('l) then
        (if sint x - sint y < - (2 ^ (LENGTH('l) - Suc 0)) then word_of_int (- (2 ^ (LENGTH('l) - Suc 0)))
         else if 2 ^ (LENGTH('l) - Suc 0) \<le> sint x - sint y then word_of_int (2 ^ (LENGTH('l) - Suc 0) - 1)
         else word_of_int (sint x - sint y))
      else if x < y then 0 else x - y)\<rangle> in
      make_function_contract pre post\<close>

lemma saturating_sub_spec [crush_specs]:
  shows \<open>\<Gamma> ; saturating_sub x y \<Turnstile>\<^sub>F saturating_sub_contract x y\<close>
by (crush_boot f: saturating_sub_def contract: saturating_sub_contract_def)
  (crush_base simp add: word_sub_saturating_core_def)

definition div_ceil_contract :: \<open>'l::{len} word \<Rightarrow> 'l word \<Rightarrow> ('machine::{sepalg}, 'l word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>div_ceil_contract x y \<equiv>
    let pre  = \<langle>is_signed TYPE('l) \<longrightarrow>
                  y \<noteq> 0 \<and> (sint x = - (2 ^ (LENGTH('l) - Suc 0)) \<longrightarrow> y \<noteq> -1)\<rangle>;
        post = \<lambda>ret. \<langle>ret = (
          if is_signed TYPE('l) then
            word_of_int (- ((- sint x) div sint y))
          else (x + y - 1) div y)\<rangle>
     in make_function_contract pre post\<close>

lemma div_ceil_spec [crush_specs]:
  shows \<open>\<Gamma> ; div_ceil x y \<Turnstile>\<^sub>F div_ceil_contract x y\<close>
by (crush_boot f: div_ceil_def contract: div_ceil_contract_def)
  (crush_base simp add: div_ceil_pure_def; (auto)?)

section\<open>\<^verbatim>\<open>NonZeroU64\<close>\<close>

typedef nonzero_u64 = \<open>{ w::64 word. w \<noteq> 0 }\<close>
  morphisms nonzero_u64_project nonzero_u64_inject
proof -
  have \<open>1 \<in> { w::64 word. w \<noteq> 0 }\<close>
    by simp
  from this show ?thesis
    by blast
qed

setup_lifting type_definition_nonzero_u64

lift_definition (code_dt) nonzerou64_new_core :: \<open>64 word \<Rightarrow> nonzero_u64 option\<close> is
  \<open>\<lambda>(n::64 word). if n = 0 then None else Some n\<close> by simp

definition nonzerou64_new :: \<open>64 word \<Rightarrow> ('machine, nonzero_u64 option, 'abort, 'i, 'o) function_body\<close> where
  \<open>nonzerou64_new n \<equiv> FunctionBody (literal (nonzerou64_new_core n))\<close>
micro_rust_notation (call) nonzerou64_new ("NonZeroU64::new")

definition nonzerou64_new_contract :: \<open>64 word \<Rightarrow>
      ('machine::{sepalg}, nonzero_u64 option, 'b) function_contract\<close> where
  [crush_contracts]: \<open>nonzerou64_new_contract n \<equiv>
     let pre  = emp;
         post = \<lambda>res. \<langle>res = nonzerou64_new_core n\<rangle>
      in make_function_contract pre post\<close>

lemma nonzerou64_new_spec [crush_specs]:
  shows \<open>\<Gamma> ; nonzerou64_new n \<Turnstile>\<^sub>F nonzerou64_new_contract n\<close>
by (crush_boot f: nonzerou64_new_def contract: nonzerou64_new_contract_def) (crush_base simp add: nonzerou64_new_core_def)

definition nonzerou64_get :: \<open>nonzero_u64 \<Rightarrow> ('machine, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>nonzerou64_get self \<equiv> FunctionBody (literal (nonzero_u64_project self))\<close>

definition nonzerou64_get_contract :: \<open>nonzero_u64 \<Rightarrow> ('machine::{sepalg}, 64 word, 'b) function_contract\<close> where
  [crush_contracts]: \<open>nonzerou64_get_contract nz \<equiv>
     let pre  = emp;
         post = \<lambda>res. \<langle>res = nonzero_u64_project nz\<rangle>
      in make_function_contract pre post\<close>

lemma nonzero_u64_get_spec [crush_specs]:
  shows \<open>\<Gamma> ; nonzerou64_get nz \<Turnstile>\<^sub>F nonzerou64_get_contract nz\<close>
by (crush_boot f: nonzerou64_get_def contract: nonzerou64_get_contract_def) crush_base

section\<open>\<^verbatim>\<open>NonZeroI64\<close>\<close>

typedef nonzero_i64 = \<open>{ w::64 sword. w \<noteq> 0 }\<close>
  morphisms nonzero_i64_project nonzero_i64_inject
proof -
  have \<open>1 \<in> { w::64 sword. w \<noteq> 0 }\<close>
    by simp
  from this show ?thesis
    by blast
qed

setup_lifting type_definition_nonzero_i64

lift_definition (code_dt) nonzeroi64_new_core :: \<open>64 sword \<Rightarrow> nonzero_i64 option\<close> is
  \<open>\<lambda>(n::64 sword). if n = 0 then None else Some n\<close> by simp

definition nonzeroi64_new :: \<open>64 sword \<Rightarrow> ('machine, nonzero_i64 option, 'abort, 'i, 'o) function_body\<close> where
  \<open>nonzeroi64_new n \<equiv> FunctionBody (literal (nonzeroi64_new_core n))\<close>
micro_rust_notation (call) nonzeroi64_new ("NonZeroI64::new")

definition nonzeroi64_new_contract :: \<open>64 sword \<Rightarrow>
      ('machine::{sepalg}, nonzero_i64 option, 'b) function_contract\<close> where
  [crush_contracts]: \<open>nonzeroi64_new_contract n \<equiv>
     let pre  = emp;
         post = \<lambda>res. \<langle>res = nonzeroi64_new_core n\<rangle>
      in make_function_contract pre post\<close>

lemma nonzeroi64_new_spec [crush_specs]:
  shows \<open>\<Gamma> ; nonzeroi64_new n \<Turnstile>\<^sub>F nonzeroi64_new_contract n\<close>
by (crush_boot f: nonzeroi64_new_def contract: nonzeroi64_new_contract_def) (crush_base simp add: nonzeroi64_new_core_def)

definition nonzeroi64_get :: \<open>nonzero_i64 \<Rightarrow> ('machine, 64 sword, 'abort, 'i, 'o) function_body\<close> where
  \<open>nonzeroi64_get self \<equiv> FunctionBody (literal (nonzero_i64_project self))\<close>

definition nonzeroi64_get_contract :: \<open>nonzero_i64 \<Rightarrow> ('machine::{sepalg}, 64 sword, 'b) function_contract\<close> where
  [crush_contracts]: \<open>nonzeroi64_get_contract nz \<equiv>
     let pre  = emp;
         post = \<lambda>res. \<langle>res = nonzero_i64_project nz\<rangle>
      in make_function_contract pre post\<close>

lemma nonzero_i64_get_spec [crush_specs]:
  shows \<open>\<Gamma> ; nonzeroi64_get nz \<Turnstile>\<^sub>F nonzeroi64_get_contract nz\<close>
by (crush_boot f: nonzeroi64_get_def contract: nonzeroi64_get_contract_def) crush_base

text\<open>The integer functions branch on \<^const>\<open>is_signed\<close> and are unfolded into their uses at
concrete word lengths for code generation (see \<^verbatim>\<open>Signedness\<close>).\<close>

declare overflowing_mul_def[abs_def, code_unfold] overflowing_add_def[abs_def, code_unfold]
  word_sub_saturating_core_def[abs_def, code_unfold] saturating_sub_def[abs_def, code_unfold]
  checked_mul_core_def[abs_def, code_unfold] checked_add_core_def[abs_def, code_unfold]
  checked_mul_def[abs_def, code_unfold] checked_add_def[abs_def, code_unfold]
  div_ceil_pure_def[abs_def, code_unfold] div_ceil_def[abs_def, code_unfold]

(*<*)
end
(*>*)
