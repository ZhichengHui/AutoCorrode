(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Signedness
  imports
    "HOL-Library.Word"
    Word_Lib.Signed_Words
    Word_Lib.Signed_Division_Word
begin
(*>*)

section\<open>Signedness of word lengths\<close>

text\<open>Signed integers are represented as \<^typ>\<open>'l signed word\<close> (\<^typ>\<open>'l sword\<close>), unsigned
integers as \<^typ>\<open>'l word\<close>. The two are distinguished by the length type: \<^typ>\<open>'l signed\<close> is
signed, the numeral length types are unsigned. \<^term>\<open>is_signed TYPE('l)\<close> reads this off the
length type. It is defined per type constructor, without a type class, so that it adds no sort
constraint; on a length type variable its value is unspecified.\<close>

consts is_signed :: \<open>'a itself \<Rightarrow> bool\<close>

overloading
  is_signed_num1 \<equiv> \<open>is_signed :: num1 itself \<Rightarrow> bool\<close>
  is_signed_bit0 \<equiv> \<open>is_signed :: 'a bit0 itself \<Rightarrow> bool\<close>
  is_signed_bit1 \<equiv> \<open>is_signed :: 'a bit1 itself \<Rightarrow> bool\<close>
  is_signed_signed \<equiv> \<open>is_signed :: 'a signed itself \<Rightarrow> bool\<close>
begin

definition is_signed_num1 :: \<open>num1 itself \<Rightarrow> bool\<close> where
  \<open>is_signed_num1 _ \<equiv> False\<close>

definition is_signed_bit0 :: \<open>'a bit0 itself \<Rightarrow> bool\<close> where
  \<open>is_signed_bit0 _ \<equiv> False\<close>

definition is_signed_bit1 :: \<open>'a bit1 itself \<Rightarrow> bool\<close> where
  \<open>is_signed_bit1 _ \<equiv> False\<close>

definition is_signed_signed :: \<open>'a signed itself \<Rightarrow> bool\<close> where
  \<open>is_signed_signed _ \<equiv> True\<close>

end

lemma is_signed_simps [simp]:
  shows \<open>\<not> is_signed TYPE(num1)\<close>
    and \<open>\<not> is_signed TYPE('a bit0)\<close>
    and \<open>\<not> is_signed TYPE('a bit1)\<close>
    and \<open>is_signed TYPE('a signed)\<close>
  by (simp_all add: is_signed_num1_def is_signed_bit0_def is_signed_bit1_def is_signed_signed_def)

section\<open>Comparisons and casts following the signedness\<close>

text\<open>Rust compares signed integers as signed and unsigned integers as unsigned.\<close>

definition word_rust_lt :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> bool\<close> where
  \<open>word_rust_lt a b \<equiv> if is_signed TYPE('l) then a <s b else a < b\<close>

definition word_rust_le :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> bool\<close> where
  \<open>word_rust_le a b \<equiv> if is_signed TYPE('l) then a \<le>s b else a \<le> b\<close>

lemma word_rust_lt_unsigned [simp]:
  assumes \<open>\<not> is_signed TYPE('l)\<close>
  shows \<open>word_rust_lt (a :: 'l::len word) b \<longleftrightarrow> a < b\<close>
  using assms by (simp add: word_rust_lt_def)

lemma word_rust_lt_signed [simp]:
  assumes \<open>is_signed TYPE('l)\<close>
  shows \<open>word_rust_lt (a :: 'l::len word) b \<longleftrightarrow> a <s b\<close>
  using assms by (simp add: word_rust_lt_def)

lemma word_rust_le_unsigned [simp]:
  assumes \<open>\<not> is_signed TYPE('l)\<close>
  shows \<open>word_rust_le (a :: 'l::len word) b \<longleftrightarrow> a \<le> b\<close>
  using assms by (simp add: word_rust_le_def)

lemma word_rust_le_signed [simp]:
  assumes \<open>is_signed TYPE('l)\<close>
  shows \<open>word_rust_le (a :: 'l::len word) b \<longleftrightarrow> a \<le>s b\<close>
  using assms by (simp add: word_rust_le_def)

text\<open>Rust's \<^verbatim>\<open>as\<close> between integer types sign-extends a signed source and zero-extends an
unsigned source, then truncates to the target width.\<close>

definition word_rust_cast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close> where
  \<open>word_rust_cast w \<equiv> if is_signed TYPE('a) then scast w else ucast w\<close>

lemma word_rust_cast_unsigned [simp]:
  assumes \<open>\<not> is_signed TYPE('a)\<close>
  shows \<open>(word_rust_cast (w :: 'a::len word) :: 'b::len word) = ucast w\<close>
  using assms by (simp add: word_rust_cast_def)

lemma word_rust_cast_signed [simp]:
  assumes \<open>is_signed TYPE('a)\<close>
  shows \<open>(word_rust_cast (w :: 'a::len word) :: 'b::len word) = scast w\<close>
  using assms by (simp add: word_rust_cast_def)

lemma word_rust_cast_unsigned_comp [simp]:
  assumes \<open>\<not> is_signed TYPE('a)\<close>
  shows \<open>(word_rust_cast :: 'a::len word \<Rightarrow> 'b::len word) = ucast\<close>
  using assms by (simp add: word_rust_cast_def fun_eq_iff)

lemma word_rust_cast_signed_comp [simp]:
  assumes \<open>is_signed TYPE('a)\<close>
  shows \<open>(word_rust_cast :: 'a::len word \<Rightarrow> 'b::len word) = scast\<close>
  using assms by (simp add: word_rust_cast_def fun_eq_iff)

section\<open>Checking specifications for unsigned operations on signed words\<close>

text\<open>On every word type, including \<^typ>\<open>'l sword\<close>, HOL's default order, division and the
constants derived from the order read the word as unsigned. In a specification about a signed
integer this is almost always a mistake. The following check runs after type inference and
reports an error when one of these constants is used at a type involving a signed word. It can be
switched off locally with \<^verbatim>\<open>declare [[urust_signed_order_check = false]]\<close>.\<close>

ML\<open>
structure Signed_Order_Check =
struct

val enabled = Attrib.setup_config_bool \<^binding>\<open>urust_signed_order_check\<close> (K true);

val unsigned_consts =
  [\<^const_name>\<open>less\<close>, \<^const_name>\<open>less_eq\<close>, \<^const_name>\<open>divide\<close>, \<^const_name>\<open>modulo\<close>,
   \<^const_name>\<open>min\<close>, \<^const_name>\<open>max\<close>, \<^const_name>\<open>Max\<close>, \<^const_name>\<open>Min\<close>,
   \<^const_name>\<open>atLeast\<close>, \<^const_name>\<open>atMost\<close>, \<^const_name>\<open>greaterThan\<close>, \<^const_name>\<open>lessThan\<close>,
   \<^const_name>\<open>atLeastAtMost\<close>, \<^const_name>\<open>atLeastLessThan\<close>,
   \<^const_name>\<open>greaterThanAtMost\<close>, \<^const_name>\<open>greaterThanLessThan\<close>];

fun is_signed_word (Type (\<^type_name>\<open>word\<close>, [Type (\<^type_name>\<open>signed\<close>, _)])) = true
  | is_signed_word _ = false;

fun check ctxt t =
  if not (Config.get ctxt enabled) then ()
  else
    Term.fold_aterms
      (fn Const (c, T) => (fn () =>
            if member (op =) unsigned_consts c andalso Term.exists_subtype is_signed_word T
            then error (Pretty.string_of (Pretty.block
              [Pretty.str "Unsigned reading of a signed word: ",
               Syntax.pretty_term ctxt (Const (c, T)), Pretty.brk 1,
               Pretty.str ":: ", Syntax.pretty_typ ctxt T, Pretty.fbrk,
               Pretty.str "On signed words, use <s, \<le>s, sint, sdiv or smod; disable this check with",
               Pretty.brk 1, Pretty.str "[[urust_signed_order_check = false]]."]))
            else ())
        | _ => I) t ();

val _ = Context.>>
  (Syntax_Phases.term_check 1 "urust_signed_order_check"
     (fn ctxt => fn ts => (List.app (check ctxt) ts; ts)));

end
\<close>

section\<open>Code generation\<close>

text\<open>\<^const>\<open>is_signed\<close> has no code equations: it is defined per type constructor, and a
code equation must hold at its most general type. Definitions that branch on it are therefore
unfolded into their monomorphic uses (\<^verbatim>\<open>code_unfold\<close>), where \<^verbatim>\<open>is_signed_simps\<close>
evaluate the branch. Code is generated only for uses at concrete word lengths.\<close>

declare is_signed_simps[code_unfold]
  word_rust_lt_def[abs_def, code_unfold] word_rust_le_def[abs_def, code_unfold] word_rust_cast_def[abs_def, code_unfold]

(*<*)
end
(*>*)
