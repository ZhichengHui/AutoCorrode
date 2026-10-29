(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory WordAdditional
  imports "HOL-Library.Word"
    Word_Lib.Word_Lib_Sumo
    ListAdditional
begin
(*>*)


section \<open>An experimental extension for numerals and order\<close>

text \<open>This is due to Lukas Stevens, formerly a PhD student of Tobias Nipkow at TU Munich.
It is off by default and when activated ensures that the order solver
recognises numerical constants that denote machine words. Ordering relationships only work for 
machine words of fixed length.\<close>

(*To activate, use note [[numeral_aware]] in a local proof scope*)

ML \<open>
  val numeral_cfg = Attrib.setup_config_bool @{binding "numeral_aware"} (K false)
\<close>

local_setup \<open>
let
  fun numeral_hook order_kind {eq, le, lt} ctxt decomp_prems =
    if Config.get ctxt numeral_cfg then
    let
      val nums =
        decomp_prems
        |> maps (fn (_, (_, _, (t1, t2))) => [t1, t2])
        |> maps (try (HOLogic.dest_number #> snd) #> the_list)
        |> sort_distinct int_ord
      val num_pairs = take (length nums - 1) nums ~~ drop 1 nums
      val ty = Term.argument_type_of eq 0
      val mk_lt_num_pair =
        apply2 (HOLogic.mk_number ty)
        #> (fn (n1, n2) => lt $ n1 $ n2)
        #> HOLogic.mk_Trueprop
      fun num_pair_thm (n1, n2) =
        Goal.prove ctxt [] [] (mk_lt_num_pair (n1, n2))
          (fn {prems, context} => simp_tac context 1)
    in
      maps (try num_pair_thm #> the_list) num_pairs
    end
    else []
in
  HOL_Base_Order_Tac.declare_insert_prems_hook (@{binding \<open>numerals\<close>}, numeral_hook)
end
\<close>

section \<open>Lemmas for reasoning about inequalities\<close>

text\<open>Our strategy for dealing with inequalities between instances \<^type>\<open>nat\<close> and
\<^type>\<open>word\<close> is to always reduce them to inequalities between natural numbers, and
to simplify any compound expressions involving word casts and word to nat conversion.\<close>

named_theorems word_nat_intros
named_theorems word_nat_elims
named_theorems word_nat_intros_weak
named_theorems word_nat_simps

lemma lt_word_to_natI [word_nat_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>unat a < unat b\<close>
    shows \<open>a < b\<close>
by (simp add: assms word_less_nat_alt)

lemma lt_sword_to_intI [word_nat_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>sint a < sint b\<close>
    shows \<open>a <s b\<close>
by (simp add: assms word_sless_alt)

text\<open>This is \<^verbatim>\<open>Word.unat_mono\<close> in another guise!\<close>
lemma lt_word_to_natE [elim_format, word_nat_elims]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>a < b\<close>
    shows \<open>unat a < unat b\<close>
using assms word_less_iff_unsigned by blast

text\<open>The signed counterpart of \<^verbatim>\<open>Word.unat_mono\<close>.\<close>
lemma sint_mono:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>a <s b\<close>
    shows \<open>sint a < sint b\<close>
using assms word_sless_alt by blast

lemma lt_sword_to_intE [elim_format, word_nat_elims]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>a <s b\<close>
    shows \<open>sint a < sint b\<close>
using assms word_sless_alt by blast

lemma unat_ucast_up:
    fixes x :: \<open>'k::{len} word\<close>
  assumes \<open>LENGTH('k) \<le> LENGTH('l::{len})\<close>
    shows \<open>unat (ucast x :: 'l word) = unat x\<close>
by (metis assms unat_ucast_up_simp)

lemma unat_ucast_16_to_64 [word_nat_simps]:
  fixes x :: \<open>16 word\<close>
  shows \<open>unat x = unat (ucast x::64 word)\<close>
using unat_ucast_up[where 'k=16 and 'l=64] by auto

lemma unat_ucast_dec:
  fixes x :: \<open>'k::{len} word\<close>
  shows \<open>unat ((ucast x) :: 'l::{len} word) \<le> unat x\<close>
by (simp add: word_unat_less_le)

lemma unat_ucast_eq [word_nat_simps]:
    fixes x :: \<open>nat\<close>
  assumes \<open>x < 2^LENGTH('k :: len)\<close>
    shows \<open>unat (word_of_nat x :: 'k word) = x\<close>
by (simp add: assms of_nat_inverse)

lemma sint_ucast_eq [word_nat_simps]:
    fixes x :: \<open>int\<close>
  assumes \<open>- (2 ^ (LENGTH('k::{len}) - Suc 0)) \<le> x\<close>
      and \<open>x < 2 ^ (LENGTH('k) - Suc 0)\<close>
    shows \<open>sint (word_of_int x :: 'k sword) = x\<close>
by (simp add: assms signed_of_int signed_take_bit_int_eq_self)

lemma ucast_ucast_eq:
    fixes x :: \<open>'l::{len} word\<close>
  assumes \<open>unat x < 2^LENGTH('k::{len})\<close>
    shows \<open>ucast (ucast x::'k word) = x\<close>
by (metis assms bintr_uint take_bit_nat_eq_self unsigned_ucast_eq unsigned_word_eqI order_refl)

lemma ucast_ucast_16_64_eq [word_nat_simps]:
    fixes x :: \<open>64 word\<close>
  assumes \<open>unat x < 2^16\<close>
    shows \<open>ucast ((ucast x)::16 word) = x\<close>
using assms ucast_ucast_eq[where 'l=64 and 'k=16] by auto

section \<open>Some facts about words and nats\<close>

lemma min_unat [simp]:
  fixes a b :: \<open>'l::{len} word\<close>
  shows \<open>min (unat a) (unat b) = unat(min a b)\<close>
by (metis min_def word_less_eq_iff_unsigned)

lemma unat_lt_twice [simp]:
  fixes a b :: \<open>'l::{len} word\<close>
    and c :: nat
  shows \<open>c < unat a \<and> c < unat b \<longleftrightarrow> c < unat(min a b)\<close>
by (metis min_less_iff_conj min_unat)

text\<open>The signed counterparts of \<^verbatim>\<open>min_unat\<close> and \<^verbatim>\<open>unat_lt_twice\<close> are false: \<^term>\<open>min\<close> on
\<^typ>\<open>'l sword\<close> follows the unsigned order. For \<^term>\<open>a = (-1 :: 8 sword)\<close> and \<^term>\<open>b = (0 :: 8 sword)\<close>,
\<^term>\<open>min a b = 0\<close>, so \<^term>\<open>sint (min a b) = 0\<close> while \<^term>\<open>min (sint a) (sint b) = -1\<close>; with
\<^term>\<open>c = (-1 :: int)\<close>, \<^term>\<open>c < sint (min a b)\<close> holds but \<^term>\<open>c < sint a\<close> does not.\<close>

lemma nat_upd_nth:
  assumes \<open>i < n\<close>
    shows \<open>[0..<n] ! i = i\<close>
using assms by simp

lemma word_unat_lt:
  assumes \<open>i < j\<close>
      and \<open>j < 2^LENGTH('l::{len})\<close>
    shows \<open>((word_of_nat i)::'l word) < word_of_nat j\<close>
by (metis assms dual_order.strict_trans2 nless_le of_nat_inverse word_less_iff_unsigned)

lemma sword_sint_lt:
  assumes \<open>i < j\<close>
      and \<open>- (2 ^ (LENGTH('l::{len}) - Suc 0)) \<le> i\<close>
      and \<open>j < 2 ^ (LENGTH('l) - Suc 0)\<close>
    shows \<open>((word_of_int i)::'l sword) <s word_of_int j\<close>
proof -
  have \<open>i < 2 ^ (LENGTH('l) - Suc 0)\<close> and \<open>- (2 ^ (LENGTH('l) - Suc 0)) \<le> j\<close>
    using assms by linarith+
  with assms show ?thesis
    by (simp add: word_sless_alt sint_ucast_eq)
qed

lemma ucast_ucast_le:
  fixes x :: \<open>'k::{len} word\<close>
  shows \<open>ucast ((ucast x)::'l::{len} word) \<le> x\<close>
by (simp add: le_ucast_ucast_le)

lemma unat_ucast_lt:
    fixes x :: \<open>'k::{len} word\<close>
      and y :: \<open>'k word\<close>
  assumes \<open>x < y\<close>
    shows \<open>unat ((ucast x)::'l::{len} word) < unat y\<close>
using unat_ucast_dec assms order_le_less_trans unat_mono by fast

lemma unat_lt_weakenI:
    fixes x  :: \<open>'k::{len} word\<close>
      and x' :: \<open>'k word\<close>
      and y :: \<open>nat\<close>
  assumes \<open>x < x'\<close>
      and \<open>unat x' \<le> y\<close>
    shows \<open>unat x < y\<close>
using assms by (meson order_less_le_trans unat_mono)

lemma sint_lt_weakenI:
    fixes x  :: \<open>'k::{len} sword\<close>
      and x' :: \<open>'k sword\<close>
      and y :: \<open>int\<close>
  assumes \<open>x <s x'\<close>
      and \<open>sint x' \<le> y\<close>
    shows \<open>sint x < y\<close>
using assms by (simp add: word_sless_alt)

lemma unat_ucast_le:
    fixes x :: \<open>'k::{len} word\<close>
      and y :: \<open>'k word\<close>
  assumes \<open>x \<le> y\<close>
    shows \<open>unat ((ucast x)::'l::{len} word) \<le> unat y\<close>
using unat_ucast_dec assms le_trans word_le_nat_alt by fast

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma unat_le_weakenI:
    fixes x  :: \<open>'k::{len} word\<close>
      and x' :: \<open>'k word\<close>
      and y :: \<open>nat\<close>
  assumes \<open>x \<le> x'\<close>
      and \<open>unat x' \<le> y\<close>
    shows \<open>unat x \<le> y\<close>
using assms by (meson dual_order.trans word_less_eq_iff_unsigned)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sint_le_weakenI:
    fixes x  :: \<open>'k::{len} sword\<close>
      and x' :: \<open>'k sword\<close>
      and y :: \<open>int\<close>
  assumes \<open>x \<le>s x'\<close>
      and \<open>sint x' \<le> y\<close>
    shows \<open>sint x \<le> y\<close>
using assms by (simp add: word_sle_eq)

lemma unat_lt_diff_len:
    fixes x :: \<open>'k::{len} word\<close>
      and y :: \<open>'l::{len} word\<close>
  assumes \<open>LENGTH('k) \<le> LENGTH('l)\<close>
    shows \<open>unat x < unat y \<longleftrightarrow> ucast x < y\<close>
using assms by (metis is_up.rep_eq linorder_not_le not_less_iff_gr_or_eq ucast_up_ucast_id
    unat_lt_weakenI unat_ucast_dec)

lemma unat_lt_16_64:
  fixes x :: \<open>16 word\<close>
    and y :: \<open>64 word\<close>
  shows \<open>unat x < unat y \<longleftrightarrow> ucast x < y\<close>
using unat_lt_diff_len[where 'k=16 and 'l=64] by auto

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma unat_ucast_adjoint:
    fixes x  :: \<open>'k::{len} word\<close>
      and y :: \<open>nat\<close>
  assumes \<open>y < 2^LENGTH('k)\<close>
    shows \<open>unat x < y \<longleftrightarrow> x < word_of_nat y\<close>
by (metis assms of_nat_inverse word_less_iff_unsigned)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sint_ucast_adjoint:
    fixes x  :: \<open>'k::{len} sword\<close>
      and y :: \<open>int\<close>
  assumes \<open>- (2 ^ (LENGTH('k) - Suc 0)) \<le> y\<close>
      and \<open>y < 2 ^ (LENGTH('k) - Suc 0)\<close>
    shows \<open>sint x < y \<longleftrightarrow> x <s word_of_int y\<close>
by (simp add: assms word_sless_alt sint_ucast_eq)

lemma word_range_sorted:
    fixes M N :: nat
  assumes \<open>0 \<le> M\<close>
      and \<open>M < N\<close>
      and \<open>N < 2^LENGTH('l::{len})\<close>
    shows \<open>sorted (List.map (Word.word_of_nat :: nat \<Rightarrow> 'l word) [M..<N])\<close>
using assms by (auto simp add: of_nat_inverse word_of_nat_le intro!: sorted_list_map_mono sorted_upt)

lemma sword_range_sorted:
    fixes M N :: int
  assumes \<open>- (2 ^ (LENGTH('l::{len}) - Suc 0)) \<le> M\<close>
      and \<open>M < N\<close>
      and \<open>N < 2 ^ (LENGTH('l) - Suc 0)\<close>
    shows \<open>sorted_wrt (\<le>s) (List.map (word_of_int :: int \<Rightarrow> 'l sword) [M..N - 1])\<close>
unfolding sorted_wrt_map
proof (rule sorted_wrt_mono_rel[OF _ sorted_upto])
  fix x y
  assume \<open>x \<in> set [M..N - 1]\<close> \<open>y \<in> set [M..N - 1]\<close> \<open>x \<le> y\<close>
  then have \<open>M \<le> x\<close> \<open>x \<le> N - 1\<close> \<open>M \<le> y\<close> \<open>y \<le> N - 1\<close>
    by auto
  with assms have \<open>- (2 ^ (LENGTH('l) - Suc 0)) \<le> x\<close> \<open>x < 2 ^ (LENGTH('l) - Suc 0)\<close>
    and \<open>- (2 ^ (LENGTH('l) - Suc 0)) \<le> y\<close> \<open>y < 2 ^ (LENGTH('l) - Suc 0)\<close>
    by linarith+
  with \<open>x \<le> y\<close> show \<open>(word_of_int x :: 'l sword) \<le>s word_of_int y\<close>
    by (simp add: word_sle_eq sint_ucast_eq)
qed

lemma add_word_lessI:
    fixes a :: \<open>'a::{len} word\<close>
  assumes \<open>n \<le> b\<close> \<open>a + word_of_nat b < c\<close>
      and \<open>unat a + b < 2 ^ LENGTH('a)\<close>
    shows \<open>a + word_of_nat n < c\<close>
proof -
  from assms have \<open>a + word_of_nat n \<le> a + word_of_nat b\<close>
    by (metis add.commute add_lessD1 unat_of_nat_eq word_add_le_mono2 word_of_nat_le)
  with assms show ?thesis
    by simp
qed

lemma add_sword_lessI:
    fixes a :: \<open>'a::{len} sword\<close>
  assumes \<open>n \<le> b\<close> \<open>a + word_of_int b <s c\<close>
      and \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> sint a + n\<close>
      and \<open>sint a + b < 2 ^ (LENGTH('a) - Suc 0)\<close>
    shows \<open>a + word_of_int n <s c\<close>
proof -
  have \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> sint a + n\<close> \<open>sint a + n < 2 ^ (LENGTH('a) - Suc 0)\<close>
    and \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> sint a + b\<close> \<open>sint a + b < 2 ^ (LENGTH('a) - Suc 0)\<close>
    using assms by linarith+
  from sint_ucast_eq[OF this(1,2)] sint_ucast_eq[OF this(3,4)]
  have \<open>sint (a + word_of_int n) = sint a + n\<close> \<open>sint (a + word_of_int b) = sint a + b\<close>
    by simp_all
  with assms(1,2) show ?thesis
    by (simp add: word_sless_alt)
qed

lemma set_of_wordlist:
    fixes M N :: \<open>nat\<close>
  assumes \<open>0 \<le> M\<close>
      and \<open>M < N\<close>
      and \<open>N < 2^LENGTH('l::{len})\<close>
    shows \<open>set (List.map Word.of_nat [M..<N]) = {v::'l word. Word.of_nat M \<le> v \<and> v < Word.of_nat N}\<close>
proof -
  from assms have \<open>\<And>a::'l word. word_of_nat M \<le> a \<Longrightarrow> a < word_of_nat N \<Longrightarrow> \<exists>b\<ge>M. b < N \<and> a = word_of_nat b\<close>
    by (metis const_le_unat order.strict_trans unat_less_helper word_unat.Rep_inverse)
  then show ?thesis
    using assms by (auto simp: of_nat_inverse word_of_nat_le word_of_nat_less image_iff Bex_def)
qed

lemma set_of_swordlist:
    fixes M N :: \<open>int\<close>
  assumes \<open>- (2 ^ (LENGTH('l::{len}) - Suc 0)) \<le> M\<close>
      and \<open>M < N\<close>
      and \<open>N < 2 ^ (LENGTH('l) - Suc 0)\<close>
    shows \<open>set (List.map word_of_int [M..N - 1]) = {v::'l sword. word_of_int M \<le>s v \<and> v <s word_of_int N}\<close>
proof -
  have M: \<open>sint (word_of_int M :: 'l sword) = M\<close> and N: \<open>sint (word_of_int N :: 'l sword) = N\<close>
    using assms by (simp_all add: sint_ucast_eq)
  have \<open>v \<in> {v::'l sword. word_of_int M \<le>s v \<and> v <s word_of_int N}\<close>
    if \<open>M \<le> k\<close> \<open>k \<le> N - 1\<close> \<open>v = word_of_int k\<close> for k v
  proof -
    from that assms have \<open>- (2 ^ (LENGTH('l) - Suc 0)) \<le> k\<close> \<open>k < 2 ^ (LENGTH('l) - Suc 0)\<close>
      by linarith+
    with that M N show ?thesis
      by (simp add: word_sle_eq word_sless_alt sint_ucast_eq)
  qed
  moreover have \<open>v \<in> set (List.map word_of_int [M..N - 1])\<close>
    if \<open>word_of_int M \<le>s v\<close> \<open>v <s word_of_int N\<close> for v :: \<open>'l sword\<close>
  proof -
    from that M N have \<open>M \<le> sint v\<close> \<open>sint v \<le> N - 1\<close>
      by (simp_all add: word_sle_eq word_sless_alt)
    then show ?thesis
      by (auto simp: image_iff intro!: bexI[of _ \<open>sint v\<close>])
  qed
  ultimately show ?thesis
    by auto
qed

lemma ucast_16_64_inj:
  assumes \<open>(ucast::16 word \<Rightarrow> 64 word) x = ucast y\<close>
    shows \<open>x = y\<close>
by (metis assms unat_ucast_16_to_64 unsigned_word_eqI)

(*<*)
context
  includes bit_operations_syntax
begin
(*>*)

lemma word_cat_0 [simp]:
  fixes x :: \<open>2 word\<close>
  shows \<open>word_cat 0 x = (ucast x::64 word)\<close>
by (simp add: word_cat_eq)

lemma unat_word_comparison:
    fixes x :: \<open>'l::{len} word\<close>
  assumes \<open>unat x = y\<close>
    shows \<open>x = Word.of_nat y\<close> and \<open>y < 2^LENGTH('l)\<close>
using assms by (auto simp add: unat_arith_simps)

lemma sint_sword_comparison:
    fixes x :: \<open>'l::{len} sword\<close>
  assumes \<open>sint x = y\<close>
    shows \<open>x = word_of_int y\<close>
      and \<open>- (2 ^ (LENGTH('l) - Suc 0)) \<le> y\<close>
      and \<open>y < 2 ^ (LENGTH('l) - Suc 0)\<close>
using assms sint_range'[of x] by auto

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma unat_word_comparisonE:
    fixes x :: \<open>'l::{len} word\<close>
  assumes \<open>unat x = y\<close>
      and \<open>x = Word.of_nat y \<Longrightarrow> y < 2^LENGTH('l) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (blast intro: unat_word_comparison)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sint_sword_comparisonE:
    fixes x :: \<open>'l::{len} sword\<close>
  assumes \<open>sint x = y\<close>
      and \<open>x = word_of_int y \<Longrightarrow> - (2 ^ (LENGTH('l) - Suc 0)) \<le> y \<Longrightarrow> y < 2 ^ (LENGTH('l) - Suc 0) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (blast intro: sint_sword_comparison)

lemma word_int_bound:
    fixes v :: \<open>'l::{len} word\<close>
      and N :: \<open>int\<close>
  assumes \<open>v \<le> Word.of_int N\<close>
      and \<open>0 \<le> N\<close>
      and \<open>N < 2^LENGTH('l)\<close>
    shows \<open>v = Word.of_int (uint v)\<close> and \<open>uint v \<le> N\<close>
using assms by (transfer, force simp add: take_bit_int_eq_self)+

lemma sword_int_bound:
    fixes v :: \<open>'l::{len} sword\<close>
      and N :: \<open>int\<close>
  assumes \<open>v \<le>s word_of_int N\<close>
      and \<open>- (2 ^ (LENGTH('l) - Suc 0)) \<le> N\<close>
      and \<open>N < 2 ^ (LENGTH('l) - Suc 0)\<close>
    shows \<open>v = word_of_int (sint v)\<close> and \<open>sint v \<le> N\<close>
using assms by (simp_all add: word_sle_eq sint_ucast_eq)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word_int_bound':
    fixes v :: \<open>'l::{len} word\<close>
      and N :: \<open>int\<close>
  assumes \<open>0 \<le> N\<close>
      and \<open>N < 2^LENGTH('l)\<close>
    shows \<open>v \<le> Word.of_int N \<longleftrightarrow> uint v \<le> N\<close>
using assms by (transfer, force simp add: take_bit_int_eq_self)+

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sword_int_bound':
    fixes v :: \<open>'l::{len} sword\<close>
      and N :: \<open>int\<close>
  assumes \<open>- (2 ^ (LENGTH('l) - Suc 0)) \<le> N\<close>
      and \<open>N < 2 ^ (LENGTH('l) - Suc 0)\<close>
    shows \<open>v \<le>s word_of_int N \<longleftrightarrow> sint v \<le> N\<close>
by (simp add: assms word_sle_eq sint_ucast_eq)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word_int_boundE:
    fixes v :: \<open>'l::{len} word\<close>
      and N :: \<open>int\<close>
  assumes \<open>v \<le> Word.of_int N\<close>
      and \<open>0 \<le> N\<close>
      and \<open>N < 2^LENGTH('l)\<close>
      and \<open>uint v \<le> N \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (blast intro: word_int_bound)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma sword_int_boundE:
    fixes v :: \<open>'l::{len} sword\<close>
      and N :: \<open>int\<close>
  assumes \<open>v \<le>s word_of_int N\<close>
      and \<open>- (2 ^ (LENGTH('l) - Suc 0)) \<le> N\<close>
      and \<open>N < 2 ^ (LENGTH('l) - Suc 0)\<close>
      and \<open>sint v \<le> N \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (blast intro: sword_int_bound)

lemma word64_bit_twiddle_technicalD1:
    fixes w :: \<open>64 word\<close>
  assumes \<open>w AND - 2 = 0\<close>
      and \<open>w AND 1 \<noteq> 1\<close>
    shows \<open>w = 0\<close>
using assms by (metis mask_eq_x_eq_0 not_one_eq word_and_1)

lemma word64_bit_twiddle_technicalD2:
    fixes w :: \<open>64 word\<close>
  assumes \<open>w AND - 2 = 0\<close>
      and \<open>w AND 1 = 0\<close>
    shows \<open>w = 0\<close>
using assms by (simp add: mask_eq_0_eq_x)

lemma word64_bit_twiddle_technicalD3:
    fixes w :: \<open>64 word\<close>
  assumes \<open>w AND - 2 = 0\<close>
      and \<open>w AND 1 = 1\<close>
    shows \<open>w = 1\<close>
using assms by (metis compl_of_1 mask_eq_x_eq_0)

lemma unat_word_of_nat64_le:
    fixes w :: \<open>64 word\<close>
  assumes \<open>unat w \<le> m\<close>
      and \<open>m < 2^64\<close>
    shows \<open>w \<le> word_of_nat m\<close>
using assms
  apply clarsimp
  apply (rule iffD2 [OF word_le_nat_alt])
  apply (subst of_nat_inverse; force)
  done

lemma sint_sword_of_int64_le:
    fixes w :: \<open>64 sword\<close>
  assumes \<open>sint w \<le> m\<close>
      and \<open>m < 2^63\<close>
    shows \<open>w \<le>s word_of_int m\<close>
proof -
  have \<open>- (2^63) \<le> sint w\<close>
    using sint_range'[of w] by simp
  with assms have \<open>- (2^63) \<le> m\<close>
    by linarith
  with assms show ?thesis
    by (simp add: word_sle_eq sint_ucast_eq)
qed

lemma unat_word_of_nat64_less:
    fixes w :: \<open>64 word\<close>
  assumes \<open>unat w < m\<close>
      and \<open>m < 2^64\<close>
    shows \<open>w < word_of_nat m\<close>
by (metis assms len32 len_bit0 numeral_Bit0_eq_double unat_less_iff)

lemma sint_sword_of_int64_less:
    fixes w :: \<open>64 sword\<close>
  assumes \<open>sint w < m\<close>
      and \<open>m < 2^63\<close>
    shows \<open>w <s word_of_int m\<close>
proof -
  have \<open>- (2^63) \<le> sint w\<close>
    using sint_range'[of w] by simp
  with assms have \<open>- (2^63) \<le> m\<close>
    by linarith
  with assms show ?thesis
    by (simp add: word_sless_alt sint_ucast_eq)
qed

lemma word_div_mul_bound:
    fixes a b c :: \<open>'l::{len} word\<close>
  assumes \<open>a \<le> b\<close>
      and \<open>i < unat ((b - a) div c)\<close>
    shows \<open>i * unat c < 2^LENGTH('l)\<close>
using assms by (metis div_lt'' le_eq_less_or_eq le_unat_uoi word_of_nat_less)

lemma word_div_mul_bound':
    fixes a b c :: \<open>'l::{len} word\<close>
  assumes \<open>a \<le> b\<close>
      and \<open>i \<le> unat ((b - a) div c)\<close>
    shows \<open>i * unat c < 2^LENGTH('l)\<close>
using assms by (metis div_lt' le_eq_less_or_eq word_div_mul_bound word_le_less_eq)

lemma le_unat_uoi':
    fixes z :: \<open>'a::{len} word\<close>
  assumes \<open>y < unat z\<close>
    shows \<open>unat (word_of_nat y::'a word) = y\<close>
using assms by (meson le_unat_uoi less_or_eq_imp_le)

lemma le_sint_soi':
    fixes z :: \<open>'a::{len} sword\<close>
  assumes \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> y\<close>
      and \<open>y < sint z\<close>
    shows \<open>sint (word_of_int y::'a sword) = y\<close>
proof -
  have \<open>y < 2 ^ (LENGTH('a) - Suc 0)\<close>
    using assms sint_range'[of z] by simp
  with assms show ?thesis
    by (simp add: sint_ucast_eq)
qed

lemma image_word_of_nat_atLeastLessThan:
  assumes \<open>a < 2 ^ LENGTH('a::{len})\<close>
      and \<open>b < 2 ^ LENGTH('a)\<close>
    shows \<open>word_of_nat ` {a..<b} = {word_of_nat a::'a word..<word_of_nat b}\<close>
proof -
  have \<open>\<exists>v\<in>{a..<b}. w = word_of_nat v\<close>
    if \<open>word_of_nat a \<le> w\<close> and \<open>w < word_of_nat b\<close> for w :: \<open>'a word\<close>
    using that assms by (metis atLeastLessThan_iff const_le_unat unat_less_helper unat_of_nat_len word_nat_cases)
  then show ?thesis
    using assms
    by (auto simp: image_iff of_nat_word_less_eq_iff of_nat_word_less_iff take_bit_nat_eq_self)
qed

lemma image_sword_of_int_atLeastLessThan:
  assumes \<open>- (2 ^ (LENGTH('a::{len}) - Suc 0)) \<le> a\<close> \<open>a < 2 ^ (LENGTH('a) - Suc 0)\<close>
      and \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> b\<close> \<open>b < 2 ^ (LENGTH('a) - Suc 0)\<close>
    shows \<open>word_of_int ` {a..<b} = {w::'a sword. word_of_int a \<le>s w \<and> w <s word_of_int b}\<close>
proof
  show \<open>word_of_int ` {a..<b} \<subseteq> {w::'a sword. word_of_int a \<le>s w \<and> w <s word_of_int b}\<close>
  proof
    fix w :: \<open>'a sword\<close>
    assume \<open>w \<in> word_of_int ` {a..<b}\<close>
    then obtain k where k: \<open>a \<le> k\<close> \<open>k < b\<close> and w: \<open>w = word_of_int k\<close>
      by auto
    from k assms have \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> k\<close> \<open>k < 2 ^ (LENGTH('a) - Suc 0)\<close>
      by linarith+
    with k w assms show \<open>w \<in> {w. word_of_int a \<le>s w \<and> w <s word_of_int b}\<close>
      by (simp add: word_sle_eq word_sless_alt sint_ucast_eq)
  qed
  show \<open>{w::'a sword. word_of_int a \<le>s w \<and> w <s word_of_int b} \<subseteq> word_of_int ` {a..<b}\<close>
  proof
    fix w :: \<open>'a sword\<close>
    assume \<open>w \<in> {w. word_of_int a \<le>s w \<and> w <s word_of_int b}\<close>
    with assms have \<open>a \<le> sint w\<close> \<open>sint w < b\<close>
      by (simp_all add: word_sle_eq word_sless_alt sint_ucast_eq)
    then show \<open>w \<in> word_of_int ` {a..<b}\<close>
      by (auto simp: image_iff intro!: bexI[of _ \<open>sint w\<close>])
  qed
qed

lemma image_word_of_nat_atLeastAtMost:
  assumes \<open>a < 2 ^ LENGTH('a::{len})\<close>
      and \<open>b < 2 ^ LENGTH('a)\<close>
    shows \<open>word_of_nat ` {a..b} = {word_of_nat a::'a word..word_of_nat b}\<close>
proof -
  have \<open>\<exists>v\<in>{a..b}. w = word_of_nat v\<close>
    if \<open>word_of_nat a \<le> w\<close> and \<open>w \<le> word_of_nat b\<close> for w :: \<open>'a word\<close>
    using that assms by (metis atLeastAtMost_iff unat_of_nat_len word_unat.Rep_inverse word_unat_less_le)
  then show ?thesis
    using assms
    by (auto simp: image_iff of_nat_word_less_eq_iff of_nat_word_less_iff take_bit_nat_eq_self)
qed

lemma image_sword_of_int_atLeastAtMost:
  assumes \<open>- (2 ^ (LENGTH('a::{len}) - Suc 0)) \<le> a\<close> \<open>a < 2 ^ (LENGTH('a) - Suc 0)\<close>
      and \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> b\<close> \<open>b < 2 ^ (LENGTH('a) - Suc 0)\<close>
    shows \<open>word_of_int ` {a..b} = {w::'a sword. word_of_int a \<le>s w \<and> w \<le>s word_of_int b}\<close>
proof
  show \<open>word_of_int ` {a..b} \<subseteq> {w::'a sword. word_of_int a \<le>s w \<and> w \<le>s word_of_int b}\<close>
  proof
    fix w :: \<open>'a sword\<close>
    assume \<open>w \<in> word_of_int ` {a..b}\<close>
    then obtain k where k: \<open>a \<le> k\<close> \<open>k \<le> b\<close> and w: \<open>w = word_of_int k\<close>
      by auto
    from k assms have \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> k\<close> \<open>k < 2 ^ (LENGTH('a) - Suc 0)\<close>
      by linarith+
    with k w assms show \<open>w \<in> {w. word_of_int a \<le>s w \<and> w \<le>s word_of_int b}\<close>
      by (simp add: word_sle_eq sint_ucast_eq)
  qed
  show \<open>{w::'a sword. word_of_int a \<le>s w \<and> w \<le>s word_of_int b} \<subseteq> word_of_int ` {a..b}\<close>
  proof
    fix w :: \<open>'a sword\<close>
    assume \<open>w \<in> {w. word_of_int a \<le>s w \<and> w \<le>s word_of_int b}\<close>
    with assms have \<open>a \<le> sint w\<close> \<open>sint w \<le> b\<close>
      by (simp_all add: word_sle_eq sint_ucast_eq)
    then show \<open>w \<in> word_of_int ` {a..b}\<close>
      by (auto simp: image_iff intro!: bexI[of _ \<open>sint w\<close>])
  qed
qed

lemma image_unat_atLeastLessThan:
  shows \<open>unat ` {a..<b} = {unat a..<unat b}\<close>
proof
  show \<open>unat ` {a..<b} \<subseteq> {unat a..<unat b}\<close>
    using unat_arith_simps(2) word_less_eq_iff_unsigned by fastforce
  have \<open>\<And>x. unat a \<le> x \<Longrightarrow> x < unat b \<Longrightarrow> word_of_nat x \<in> {a..<b}\<close>
    by (simp add: le_unat_uoi' word_le_nat_alt word_of_nat_less)
  then show \<open>{unat a..<unat b} \<subseteq> unat ` {a..<b}\<close>
    by (metis (no_types, opaque_lifting) atLeastLessThan_iff imageI le_unat_uoi' subsetI)
qed

lemma image_sint_atLeastLessThan:
  fixes a b :: \<open>'a::{len} sword\<close>
  shows \<open>sint ` {w. a \<le>s w \<and> w <s b} = {sint a..<sint b}\<close>
proof
  show \<open>sint ` {w. a \<le>s w \<and> w <s b} \<subseteq> {sint a..<sint b}\<close>
    by (auto simp: word_sle_eq word_sless_alt)
  show \<open>{sint a..<sint b} \<subseteq> sint ` {w. a \<le>s w \<and> w <s b}\<close>
  proof
    fix x
    assume \<open>x \<in> {sint a..<sint b}\<close>
    then have x: \<open>sint a \<le> x\<close> \<open>x < sint b\<close>
      by auto
    then have \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> x\<close> \<open>x < 2 ^ (LENGTH('a) - Suc 0)\<close>
      using sint_range'[of a] sint_range'[of b] by simp_all
    from sint_ucast_eq[OF this] x show \<open>x \<in> sint ` {w. a \<le>s w \<and> w <s b}\<close>
      by (auto simp: image_iff word_sle_eq word_sless_alt intro!: exI[of _ \<open>word_of_int x\<close>])
  qed
qed

lemma image_unat_atLeastAtMost:
  shows \<open>unat ` {a..b} = {unat a..unat b}\<close>
proof
  show \<open>unat ` {a..b} \<subseteq> {unat a..unat b}\<close>
    using unat_arith_simps(2) word_less_eq_iff_unsigned by fastforce
  have \<open> \<And>x. unat a \<le> x \<Longrightarrow> x \<le> unat b \<Longrightarrow> word_of_nat x \<in> {a..b}\<close>
    by (simp add: le_unat_uoi word_le_nat_alt word_of_nat_le)
  then show \<open>{unat a..unat b} \<subseteq> unat ` {a..b}\<close>
    by (metis (no_types, opaque_lifting) atLeastAtMost_iff imageI le_unat_uoi subsetI)
qed

lemma image_sint_atLeastAtMost:
  fixes a b :: \<open>'a::{len} sword\<close>
  shows \<open>sint ` {w. a \<le>s w \<and> w \<le>s b} = {sint a..sint b}\<close>
proof
  show \<open>sint ` {w. a \<le>s w \<and> w \<le>s b} \<subseteq> {sint a..sint b}\<close>
    by (auto simp: word_sle_eq)
  show \<open>{sint a..sint b} \<subseteq> sint ` {w. a \<le>s w \<and> w \<le>s b}\<close>
  proof
    fix x
    assume \<open>x \<in> {sint a..sint b}\<close>
    then have x: \<open>sint a \<le> x\<close> \<open>x \<le> sint b\<close>
      by auto
    then have \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> x\<close> \<open>x < 2 ^ (LENGTH('a) - Suc 0)\<close>
      using sint_range'[of a] sint_range'[of b] by simp_all
    from sint_ucast_eq[OF this] x show \<open>x \<in> sint ` {w. a \<le>s w \<and> w \<le>s b}\<close>
      by (auto simp: image_iff word_sle_eq intro!: exI[of _ \<open>word_of_int x\<close>])
  qed
qed

lemma nonoverflow_range:
    fixes a b :: \<open>'a::{len} word\<close>
  assumes \<open>a \<le> a + b\<close>
      and \<open>c \<le> b\<close>
    shows \<open>a \<le> a + c\<close>
using assms by unat_arith

lemma not_gr0_word:
  fixes n :: \<open>'a::{len} word\<close>
  shows \<open>\<not>0 < n \<longleftrightarrow> n = 0\<close>
by unat_arith

lemma lt_sub_left:
    fixes x y :: \<open>'a::{len} word\<close>
  assumes \<open>0 < x\<close>
      and \<open>x < y\<close>
    shows \<open>y - x < y\<close>
using assms by unat_arith

lemma lt_sub_left_sword:
    fixes x y :: \<open>'a::{len} sword\<close>
  assumes \<open>0 <s x\<close>
      and \<open>x <s y\<close>
    shows \<open>y - x <s y\<close>
proof -
  have x0: \<open>0 < sint x\<close> and xy: \<open>sint x < sint y\<close>
    using assms by (simp_all add: word_sless_alt)
  have \<open>- (2 ^ (LENGTH('a) - Suc 0)) \<le> sint y - sint x\<close> \<open>sint y - sint x < 2 ^ (LENGTH('a) - Suc 0)\<close>
    using x0 xy sint_range'[of y] by simp_all
  from sint_ucast_eq[OF this] have \<open>sint (y - x) = sint y - sint x\<close>
    by simp
  with x0 show ?thesis
    by (simp add: word_sless_alt)
qed

section \<open>Brute-force splitting of @{term\<open>w\<le>nn\<close>} or @{term\<open>w<nn\<close>} into cases\<close>

lemma word_le_numE:
    fixes m :: \<open>'a::{len} word\<close>
  assumes \<open>m \<le> numeral n\<close>
  obtains \<open>m = numeral n\<close> | \<open>m \<le> of_nat (pred_numeral n)\<close>
proof (cases \<open>m = numeral n\<close>)
  case False
  then have \<open>\<not> m \<ge> 1 + of_nat (pred_numeral n)\<close>
    by (metis assms nle_le numeral_eq_Suc of_nat_Suc of_nat_numeral)
  with that show thesis
    by (metis add.commute inc_le leI)
qed

lemma word_le_1E:
    fixes m :: \<open>'a::{len} word\<close>
  assumes \<open>m \<le> 1\<close>
  obtains \<open>m = 0\<close> | \<open>m = 1\<close>
using assms word_le_sub1 by fastforce

lemma word_less_numE:
    fixes m :: \<open>'a::{len} word\<close>
  assumes \<open>m < numeral n\<close>
  obtains \<open>m \<le> of_nat (pred_numeral n)\<close>
by (metis assms nless_le word_le_numE)

text \<open>Use with auto/force and the elim! modifiers\<close>
lemmas word_leE = word_le_numE word_le_1E word_less_numE

text \<open>A rewrite that replaces identity of words to identity of bits\<close>
lemma bit_word_eq_iff:
  fixes a b :: \<open>'a::{len} word\<close>
  shows \<open>a = b \<longleftrightarrow> (\<forall>n < LENGTH('a). bit a n \<longleftrightarrow> bit b n)\<close>
using bit_word_eqI by auto

lemma nat_le_numeral_iff:
  shows \<open>n \<le> numeral v \<longleftrightarrow> n = numeral v \<or> n \<le> pred_numeral v\<close>
by (metis Suc_eq_numeral le_Suc_eq)

lemma nat_less_numeral_iff:
  shows \<open>m < numeral n \<longleftrightarrow> m \<le> pred_numeral n\<close>
using less_eq_Suc_le by force

text \<open>Rewrites to explode a bounded quantifier into individual cases\<close>
lemmas nat_le_numeral_iffs = nat_le_numeral_iff nat_less_numeral_iff le_Suc_eq[where n=0]

text \<open>Bitwise boolean ops. Negation doesn't fit this pattern: word length intrudes\<close>
lemmas word_op_nth = word_and_nth word_or_nth word_xor_nth

lemma push_bit_drop_bit:
  assumes \<open>k \<ge> m\<close>
      and \<open>m \<ge> n\<close>
    shows \<open>bit (push_bit m (drop_bit n a)) k = bit (push_bit (m-n) a) k\<close>
using assms unfolding bit_push_bit_iff by (auto simp add: bit_iff_odd_drop_bit possible_bit_def le_imp_diff_le)

lemma mod_eq_mask:
  shows \<open>x mod (2^n) = x AND mask n\<close>
by (metis take_bit_eq_mask take_bit_eq_mod)

lemma mod16_eq_mask:
  shows \<open>x mod 0x10 = x AND mask 4\<close>
using mod_eq_mask [of x 4] by simp

text \<open>Examples of use\<close>

lemma
    fixes m :: \<open>'a::{len} word\<close>
    assumes \<open>m \<le> 6\<close>
        and \<open>P 0\<close>
        and \<open>P 1\<close>
        and \<open>P 2\<close>
        and \<open>P 3\<close>
        and \<open>P 4\<close>
        and \<open>P 5\<close>
        and \<open>P 6\<close>
    shows \<open>P m\<close>
using assms by (force elim!: word_leE)

lemma
  fixes x :: \<open>64 word\<close>
  shows \<open>x AND (push_bit 2 (mask 4)) = 0xc \<longleftrightarrow> x AND mask 6 \<in> {0xc,0xd,0xe,0xf}\<close>
  \<comment> \<open>Note: two separate steps seem necessary\<close>
by safe (auto simp: mask_eq_exp_minus_1 bit_word_eq_iff nat_le_numeral_iffs word_op_nth)

abbreviation word_align_down :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 64 word\<close> where
  \<open>word_align_down a n \<equiv> a AND NOT (mask n)\<close>

definition page_range_word :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 64 word set\<close> where
  \<open>page_range_word start n \<equiv> {start..(start + 2 ^ n - 1)}\<close>

definition block_range :: \<open>64 word \<Rightarrow> nat \<Rightarrow> 64 word set\<close> where
  \<open>block_range addr n \<equiv> { pa . word_align_down addr n = word_align_down pa n }\<close>

lemma aligned_word_range:
  assumes \<open>is_aligned start l\<close>
    shows \<open>a \<in> page_range_word start l \<longleftrightarrow> word_align_down a l = start\<close>
proof
  assume \<open>a \<in> page_range_word start l\<close>
  moreover from this have \<open>start \<le> a\<close> and \<open>a \<le> start + 2 ^ l - 1\<close>
    by (auto simp add: page_range_word_def)
  ultimately show \<open>word_align_down a l = start\<close>
    using assms by (clarsimp simp add: page_range_word_def add_mask_fold neg_mask_in_mask_range)
next
  assume \<open>word_align_down a l = start\<close>
  moreover from this have \<open>word_align_down a l \<le> a\<close>
    by (meson word_and_le2)
  moreover from calculation assms have \<open>a \<le> start + 2 ^ l - 1\<close>
    by (metis add_mask_fold and_neg_mask_plus_mask_mono)
  ultimately show \<open>a \<in> page_range_word start l\<close>
    by (clarsimp simp add: page_range_word_def)
qed

(*<*)
end (*bit_operations_syntax*)

lemma word_align_down_plus_pow2:
    fixes x :: \<open>64 word\<close>
  assumes \<open>is_aligned x (Suc n)\<close>
    shows \<open>word_align_down (x + (2^n)) n = word_align_down x n OR (2^n)\<close>
using assms by (simp add: neg_mask_add t2n_mask_eq_if is_aligned_neg_mask_weaken
  is_aligned_nth nth_is_and_neq_0 flip: disjunctive_add2)

abbreviation word64_of_nat :: \<open>nat \<Rightarrow> 64 word\<close> where
  \<open>word64_of_nat \<equiv> word_of_nat\<close>

lemma word64_div_mono:
    fixes x y z :: \<open>64 word\<close>
  assumes \<open>x \<le> y\<close>
    shows \<open>x div z \<le> y div z\<close>
using assms by (simp add: div_le_mono unat_div word_le_nat_alt)

lemma word_nth_out_of_bounds:
  fixes addr :: \<open>'l::len word\<close>
  assumes \<open>\<not>(n < LENGTH('l))\<close>
    shows \<open>addr !! n = False\<close>
using assms bit_imp_le_length by blast

lemmas word_nth_simps =
  ucast_ucast_mask is_aligned_nth less_imp_diff_less bit_mask_iff bit_drop_bit_eq bin_nth_shiftr
  neg_mask_test_bit word_or_nth word_and_nth nth_shiftl bit_or_iff bit_ucast_iff size_word_def
  bit_push_bit_iff'

lemma drop_bit_align_down:
  shows \<open>drop_bit n addr = drop_bit n (word_align_down addr n)\<close>
  apply (intro word_eqI; clarsimp simp add: word_nth_simps)
  apply (case_tac \<open>n + na < 64\<close>; simp add: word_nth_out_of_bounds)
  done

lemma UCAST_0_alt:
  fixes w :: \<open>'a::len word\<close>
  assumes \<open>LENGTH('b) \<le> LENGTH('a)\<close>
    shows \<open>UCAST('a \<rightarrow> 'b::len) w = 0 \<longleftrightarrow> is_aligned w LENGTH('b)\<close>
by (meson is_aligned_over_length is_aligned_ucastI order.refl ucast_zero_is_aligned)

lemma word_lt_elim:
    fixes x :: \<open>'a::len word\<close>
  assumes \<open>x < numeral n\<close>
      and \<open>\<And>k. k < numeral n \<Longrightarrow> x = of_nat k \<Longrightarrow> P\<close>
    shows \<open>P\<close>
using assms by (metis of_nat_numeral unat_less_helper word_unat.Rep_inverse')

lemma nat_lt_elim:
    fixes x :: \<open>nat\<close>
  assumes \<open>x < numeral n\<close>
      and \<open>\<And>k. k < numeral n \<Longrightarrow> x = k \<Longrightarrow> P\<close>
    shows \<open>P\<close>
using assms by blast

lemma ucast_collapse:
  assumes \<open>x < 2^LENGTH('m)\<close>
    shows \<open>UCAST('m::{len} \<rightarrow> 'l::{len}) (UCAST ('n::{len} \<rightarrow> 'm) x) = UCAST ('n \<rightarrow> 'l) x\<close>
using assms by (metis Word.of_nat_unat ucast_of_nat_small unat_less_helper word_unat_power)

lemma and_length_lt:
  assumes \<open>m < 2^LENGTH('l::{len})\<close>
    shows \<open>m && n < 2^LENGTH('l::{len})\<close>
using assms by (metis word_and_less' word_bw_comms(1))

lemma unat_plus_lt_fiddle:
    fixes x y z :: \<open>'a::{len} word\<close>
  assumes \<open>x \<le> x + y\<close>
    shows \<open>unat x + unat y < 2^LENGTH('a)\<close>
using assms by (subst no_plus_overflow_unat_size[simplified size_word_def, simplified, symmetric])

end
(*>*)