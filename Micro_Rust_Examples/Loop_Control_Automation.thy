(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Loop_Control_Automation
  imports Showcase
begin
(*>*)

section\<open>Proofs of loops with \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close>\<close>

context showcase_ctx
begin

lemma count_up_facts:
  fixes l v :: \<open>64 word\<close>
  shows \<open>unat v < unat l \<Longrightarrow> unat (v + 1) = Suc (unat v)\<close>
    and \<open>(v < l) = (unat v < unat l)\<close>
proof -
  assume \<open>unat v < unat l\<close>
  then have \<open>unat v + unat (1 :: 64 word) < 2 ^ LENGTH(64)\<close>
    using More_Word.unat_lt2p[of l] by simp
  then show \<open>unat (v + 1) = Suc (unat v)\<close>
    by (simp add: unat_add_lem[THEN iffD1])
next
  show \<open>(v < l) = (unat v < unat l)\<close>
    by (simp add: word_less_nat_alt)
qed

subsection\<open>\<^verbatim>\<open>return\<close> inside a loop\<close>

text\<open>The loop rule establishes \<^term>\<open>\<tau>\<close> for a \<^verbatim>\<open>return\<close> in the loop body.\<close>

definition has :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>has nums l k \<equiv> FunctionBody \<lbrakk>
    for i in 0..l {
      if nums[i] == \<llangle>k\<rrangle> {
        return \<llangle>1 :: nat\<rrangle>;
      }
    };
    \<llangle>0 :: nat\<rrangle>
  \<rbrakk>\<close>

definition has_contract :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>has_contract nums l k \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l = LENGTH('a)\<rangle> in
    let post = \<lambda> r. \<langle>r \<le> 1 \<and> (r = 1) = (k \<in> set (array_to_list nums))\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma has_spec:
  shows \<open>\<Gamma>; has nums l k \<Turnstile>\<^sub>F has_contract nums l k\<close>
proof (crush_boot f: has_def contract: has_contract_def, goal_cases)
  case 1
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow>
      (k \<in> set (take (Suc i) (array_to_list nums))) = (k \<in> set (take i (array_to_list nums)) \<or> array_nth nums i = k)\<close>
    by (auto simp add: take_Suc_conv_app_nth)
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow> array_nth nums i \<in> set (array_to_list nums)\<close>
    by (metis array_to_list_length array_to_list_nth nth_mem)
  moreover note More_Word.unat_lt2p[of l]
  ultimately show ?case
    apply crush_base
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>_ i. \<langle>k \<notin> set (take i (array_to_list nums))\<rangle>\<close> and
        BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. \<langle>r = 1 \<and> k \<in> set (array_to_list nums)\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'
    \<close>)
    by (crush_base simp add: More_Word.unat_of_nat_eq)
qed

subsection\<open>\<^verbatim>\<open>while\<close> with \<^verbatim>\<open>break\<close>\<close>

text\<open>The loop ends only by the \<^verbatim>\<open>break\<close>: by the precondition, the invariant for no fuel left is unsatisfiable.\<close>

definition count_to :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>count_to n k l \<equiv> FunctionBody \<lbrakk>
    let mut x = \<llangle>0 :: 64 word\<rrangle>;
    #[fuel(\<epsilon>\<open>n\<close>)] while (*x < \<llangle>l\<rrangle>) {
      if *x == \<llangle>k\<rrangle> {
        break;
      }
      x = *x + 1_u64;
    };
    *x
  \<rbrakk>\<close>

definition count_to_contract :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'b) function_contract\<close> where
  \<open>count_to_contract n k l \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>k < l \<and> unat k < n\<rangle> in
    let post = \<lambda> r. \<langle>r = k\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma count_to_spec:
  shows \<open>\<Gamma>; count_to n k l \<Turnstile>\<^sub>F count_to_contract n k l\<close>
proof (crush_boot f: count_to_def contract: count_to_contract_def, goal_cases)
  case 1
  then have kl: \<open>unat k < unat l\<close>
    by (simp add: word_less_nat_alt)
  have unat_x: \<open>\<And>m. m \<le> unat k \<Longrightarrow> unat (word_of_nat m :: 64 word) = m\<close>
    by (intro unat_of_nat_eq) (meson le_less_trans unat_lt2p)
  from 1 have \<open>unat k < n\<close>
    by simp
  moreover note kl
  moreover note More_Word.unat_lt2p[of l]
  moreover have \<open>\<And>v :: 64 word. unat v \<le> unat k \<Longrightarrow> v < l\<close>
    using kl by (simp add: word_less_nat_alt)
  moreover have \<open>\<And>v :: 64 word. unat v \<le> unat k \<Longrightarrow> unat (v + 1) = Suc (unat v)\<close>
  proof -
    fix v :: \<open>64 word\<close>
    assume \<open>unat v \<le> unat k\<close>
    then have \<open>unat v + unat (1 :: 64 word) < 2 ^ LENGTH(64)\<close>
      using kl More_Word.unat_lt2p[of l] by simp
    then show \<open>unat (v + 1) = Suc (unat v)\<close>
      by (simp add: unat_add_lem[THEN iffD1])
  qed
  ultimately show ?case
    apply crush_base
    subgoal for x_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>j. \<Squnion> g v. x_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>unat v = n - j \<and> n - j \<le> unat k \<and> j \<le> n\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion> g v. x_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>unat v = n - Suc j \<and> n - Suc j \<le> unat k \<and> Suc j \<le> n\<rangle>\<close> and
          BRK=\<open>\<lambda>_. \<Squnion> g. x_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>k\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI
      \<close>)
      apply (crush_base simp add: Suc_diff_Suc)
      \<comment>\<open>The automation does not relate \<^term>\<open>ra \<noteq> k\<close> to \<^term>\<open>unat ra \<noteq> unat k\<close>\<close>
      subgoal for _ _ ra
        using word_unat_eq_iff[of ra k] by auto
      done
    done
qed

subsection\<open>\<^verbatim>\<open>while\<close> with \<^verbatim>\<open>continue\<close>\<close>

text\<open>A \<^verbatim>\<open>continue\<close> establishes the invariant for the next iteration.\<close>

definition count_skip :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>count_skip n k l \<equiv> FunctionBody \<lbrakk>
    let mut x = \<llangle>0 :: 64 word\<rrangle>;
    let mut c = \<llangle>0 :: nat\<rrangle>;
    #[fuel(\<epsilon>\<open>n\<close>)] while (*x < \<llangle>l\<rrangle>) {
      x = *x + 1_u64;
      if *x == \<llangle>k\<rrangle> {
        continue;
      }
      c = *c + \<llangle>1 :: nat\<rrangle>;
    };
    *c
  \<rbrakk>\<close>

definition count_skip_contract :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>count_skip_contract n k l \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l < n \<and> 0 < k \<and> k \<le> l\<rangle> in
    let post = \<lambda> r. \<langle>r = unat l - 1\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma count_skip_spec:
  shows \<open>\<Gamma>; count_skip n k l \<Turnstile>\<^sub>F count_skip_contract n k l\<close>
proof (crush_boot f: count_skip_def contract: count_skip_contract_def, goal_cases)
  case 1
  \<comment>\<open>The value of the counter after \<^term>\<open>m\<close> iterations. It is a local definition, so that
     the automation does not split the case distinction in the invariant.\<close>
  define cnt where \<open>cnt m = (if unat k \<le> m then m - 1 else m)\<close> for m
  from 1 have kl: \<open>0 < unat k\<close> \<open>unat k \<le> unat l\<close>
    by (simp_all add: word_le_nat_alt unat_gt_0)
  have cnt_facts: \<open>\<And>m. Suc m = unat k \<Longrightarrow> cnt (Suc m) = cnt m\<close>
       \<open>\<And>m. Suc m \<noteq> unat k \<Longrightarrow> cnt (Suc m) = Suc (cnt m)\<close>
       \<open>cnt 0 = 0\<close>
       \<open>cnt (unat l) = unat l - 1\<close>
    using kl by (auto simp add: cnt_def)
  have eq_k: \<open>\<And>v :: 64 word. unat v < unat l \<Longrightarrow> (v + 1 = k) = (Suc (unat v) = unat k)\<close>
  proof -
    fix v :: \<open>64 word\<close>
    assume \<open>unat v < unat l\<close>
    then have \<open>unat (v + 1) = Suc (unat v)\<close>
      by (rule count_up_facts(1))
    moreover have \<open>(v + 1 = k) = (unat (v + 1) = unat k)\<close>
      by (rule word_unat_eq_iff)
    ultimately show \<open>(v + 1 = k) = (Suc (unat v) = unat k)\<close>
      by simp
  qed
  note 1 kl
  moreover note count_up_facts[of _ l]
  moreover note eq_k
  moreover note cnt_facts
  moreover note More_Word.unat_lt2p[of l]
  ultimately show ?case
    apply crush_base
    subgoal for x_ref c_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>j. \<Squnion> g v h. x_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> h\<down>(cnt (unat v)) \<star>
                 \<langle>unat v \<le> unat l \<and> (j = 0 \<longrightarrow> unat v = unat l) \<and> (0 < j \<longrightarrow> unat v + j \<ge> n)\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion> g v h. x_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> c_ref \<mapsto>\<langle>\<top>\<rangle> h\<down>(cnt (unat v)) \<star>
                 \<langle>unat v < unat l \<and> unat v + Suc j \<ge> n\<rangle>\<close> and
          BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI
      \<close>)
      by crush_base
    done
qed

subsection\<open>\<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> in one loop\<close>

definition sum_until :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>sum_until nums l k s \<equiv> FunctionBody \<lbrakk>
    let mut sum = \<llangle>0 :: nat\<rrangle>;
    for i in 0..l {
      let num = nums[i];
      if num == \<llangle>s\<rrangle> {
        break;
      }
      if num == \<llangle>k\<rrangle> {
        continue;
      }
      sum = *sum + num;
    };
    *sum
  \<rbrakk>\<close>

definition sum_until_contract :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>sum_until_contract nums l k s \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l = LENGTH('a)\<rangle> in
    let post = \<lambda> r. \<langle>r = sum_list (filter (\<lambda>x. x \<noteq> k) (takeWhile (\<lambda>x. x \<noteq> s) (array_to_list nums)))\<rangle>
                      \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma sum_until_spec:
  shows \<open>\<Gamma>; sum_until nums l k s \<Turnstile>\<^sub>F sum_until_contract nums l k s\<close>
proof (crush_boot f: sum_until_def contract: sum_until_contract_def, goal_cases)
  case 1
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow>
      sum_list (filter (\<lambda>x. x \<noteq> k) (take (Suc i) (array_to_list nums))) =
      sum_list (filter (\<lambda>x. x \<noteq> k) (take i (array_to_list nums))) + (if array_nth nums i = k then 0 else array_nth nums i)\<close>
    by (simp add: take_Suc_conv_app_nth)
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow>
      (s \<notin> set (take (Suc i) (array_to_list nums))) = (s \<notin> set (take i (array_to_list nums)) \<and> array_nth nums i \<noteq> s)\<close>
    by (auto simp add: take_Suc_conv_app_nth)
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow> s \<notin> set (take i (array_to_list nums)) \<Longrightarrow> array_nth nums i = s \<Longrightarrow>
      sum_list (filter (\<lambda>x. x \<noteq> k) (take i (array_to_list nums)))
        = sum_list (filter (\<lambda>x. x \<noteq> k) (takeWhile (\<lambda>x. x \<noteq> s) (array_to_list nums)))\<close>
  proof -
    fix i
    assume i: \<open>i < LENGTH('a)\<close> \<open>s \<notin> set (take i (array_to_list nums))\<close> \<open>array_nth nums i = s\<close>
    have \<open>takeWhile (\<lambda>x. x \<noteq> s) (array_to_list nums) = take i (array_to_list nums)\<close>
    proof (rule takeWhile_eq_take_P_nth)
      fix j
      assume j: \<open>j < i\<close> \<open>j < length (array_to_list nums)\<close>
      then have \<open>take i (array_to_list nums) ! j \<in> set (take i (array_to_list nums))\<close>
        by (intro nth_mem) simp
      with i(2) j show \<open>array_to_list nums ! j \<noteq> s\<close>
        by auto
    next
      show \<open>\<not> array_to_list nums ! i \<noteq> s\<close>
        using i by simp
    qed
    then show \<open>sum_list (filter (\<lambda>x. x \<noteq> k) (take i (array_to_list nums)))
        = sum_list (filter (\<lambda>x. x \<noteq> k) (takeWhile (\<lambda>x. x \<noteq> s) (array_to_list nums)))\<close>
      by simp
  qed
  moreover have \<open>s \<notin> set (array_to_list nums) \<Longrightarrow>
      sum_list (filter (\<lambda>x. x \<noteq> k) (array_to_list nums))
        = sum_list (filter (\<lambda>x. x \<noteq> k) (takeWhile (\<lambda>x. x \<noteq> s) (array_to_list nums)))\<close>
  proof -
    assume \<open>s \<notin> set (array_to_list nums)\<close>
    then have \<open>takeWhile (\<lambda>x. x \<noteq> s) (array_to_list nums) = array_to_list nums\<close>
      by (auto simp add: takeWhile_eq_all_conv)
    then show ?thesis
      by (simp del: takeWhile_eq_all_conv)
  qed
  moreover note More_Word.unat_lt2p[of l]
  ultimately show ?case
    apply crush_base
    subgoal for sum_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g. sum_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(sum_list (filter (\<lambda>x. x \<noteq> k) (take i (array_to_list nums))))
                         \<star> \<langle>s \<notin> set (take i (array_to_list nums))\<rangle>\<close> and
          BRK=\<open>\<lambda>_ _. \<Squnion> g. sum_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(sum_list (filter (\<lambda>x. x \<noteq> k) (takeWhile (\<lambda>x. x \<noteq> s) (array_to_list nums))))\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'
      \<close>)
      by (crush_base simp add: More_Word.unat_of_nat_eq)
  done
qed

subsection\<open>A labeled \<^verbatim>\<open>break\<close> out of a nested loop\<close>

text\<open>In the proof, \<^term>\<open>\<theta>\<close> of the inner loop is left to the automation; it passes \<^verbatim>\<open>break 'outer\<close> on to the outer loop.\<close>

definition common :: \<open>(nat, 'a::len) array \<Rightarrow> (nat, 'b::len) array \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
    ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>common xs ys la lb \<equiv> FunctionBody \<lbrakk>
    let mut found = \<llangle>0 :: nat\<rrangle>;
    'outer: for i in 0..la {
      for j in 0..lb {
        if xs[i] == ys[j] {
          found = \<llangle>1 :: nat\<rrangle>;
          break 'outer;
        }
      }
    };
    *found
  \<rbrakk>\<close>

definition common_contract :: \<open>(nat, 'a::len) array \<Rightarrow> (nat, 'b::len) array \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
    ('s, nat, 'c) function_contract\<close> where
  \<open>common_contract xs ys la lb \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat la = LENGTH('a) \<and> unat lb = LENGTH('b)\<rangle> in
    let post = \<lambda> r. \<langle>r \<le> 1 \<and> (r = 1) = (set (array_to_list xs) \<inter> set (array_to_list ys) \<noteq> {})\<rangle>
                      \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma common_spec:
  shows \<open>\<Gamma>; common xs ys la lb \<Turnstile>\<^sub>F common_contract xs ys la lb\<close>
proof (crush_boot f: common_def contract: common_contract_def, goal_cases)
  case 1
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow>
      (set (take (Suc i) (array_to_list xs)) \<inter> set (array_to_list ys) = {}) =
      (set (take i (array_to_list xs)) \<inter> set (array_to_list ys) = {} \<and> array_nth xs i \<notin> set (array_to_list ys))\<close>
    by (auto simp add: take_Suc_conv_app_nth)
  moreover have \<open>\<And> j a. j < LENGTH('b) \<Longrightarrow>
      (a \<notin> set (take (Suc j) (array_to_list ys))) = (a \<notin> set (take j (array_to_list ys)) \<and> array_nth ys j \<noteq> a)\<close>
    by (auto simp add: take_Suc_conv_app_nth)
  moreover have \<open>\<And> i j. i < LENGTH('a) \<Longrightarrow> j < LENGTH('b) \<Longrightarrow> array_nth xs i = array_nth ys j \<Longrightarrow>
      set (array_to_list xs) \<inter> set (array_to_list ys) \<noteq> {}\<close>
    by (metis array_to_list_length array_to_list_nth disjoint_iff nth_mem)
  moreover note More_Word.unat_lt2p[of la] More_Word.unat_lt2p[of lb]
  ultimately show ?case
    apply crush_base
    subgoal for found_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g. found_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(0 :: nat)
                         \<star> \<langle>set (take i (array_to_list xs)) \<inter> set (array_to_list ys) = {}\<rangle>\<close> and
          BRK=\<open>\<lambda>_ _. \<Squnion> g. found_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(1 :: nat)
                         \<star> \<langle>set (array_to_list xs) \<inter> set (array_to_list ys) \<noteq> {}\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'
      \<close>)
      subgoal
        by (crush_base simp add: More_Word.unat_of_nat_eq)
      subgoal for i
        apply (crush_base simp add: More_Word.unat_of_nat_eq)
        apply (ucincl_discharge\<open>
          rule_tac
            INV=\<open>\<lambda>_ j. \<Squnion> g. found_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(0 :: nat)
                         \<star> \<langle>set (take i (array_to_list xs)) \<inter> set (array_to_list ys) = {}
                            \<and> array_nth xs i \<notin> set (take j (array_to_list ys))\<rangle>\<close> and
            BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close> and
            \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_raw_for_loop_framedI'
        \<close>)
        by (crush_base simp add: More_Word.unat_of_nat_eq)
      done
  done
qed

subsection\<open>A labeled \<^verbatim>\<open>continue\<close> out of a nested loop\<close>

text\<open>In the proof, \<^term>\<open>\<theta>\<close> of the inner loop is left to the automation; it passes \<^verbatim>\<open>continue 'outer\<close> on to the outer loop.\<close>

definition count_common :: \<open>(nat, 'a::len) array \<Rightarrow> (nat, 'b::len) array \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
    ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>count_common xs ys la lb \<equiv> FunctionBody \<lbrakk>
    let mut c = \<llangle>0 :: nat\<rrangle>;
    'outer: for i in 0..la {
      for j in 0..lb {
        if xs[i] == ys[j] {
          c = *c + \<llangle>1 :: nat\<rrangle>;
          continue 'outer;
        }
      }
    };
    *c
  \<rbrakk>\<close>

definition count_common_contract :: \<open>(nat, 'a::len) array \<Rightarrow> (nat, 'b::len) array \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
    ('s, nat, 'c) function_contract\<close> where
  \<open>count_common_contract xs ys la lb \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat la = LENGTH('a) \<and> unat lb = LENGTH('b)\<rangle> in
    let post = \<lambda> r. \<langle>r = length (filter (\<lambda>x. x \<in> set (array_to_list ys)) (array_to_list xs))\<rangle>
                      \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma count_common_spec:
  shows \<open>\<Gamma>; count_common xs ys la lb \<Turnstile>\<^sub>F count_common_contract xs ys la lb\<close>
proof (crush_boot f: count_common_def contract: count_common_contract_def, goal_cases)
  case 1
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow>
      length (filter (\<lambda>x. x \<in> set (array_to_list ys)) (take (Suc i) (array_to_list xs))) =
      length (filter (\<lambda>x. x \<in> set (array_to_list ys)) (take i (array_to_list xs)))
        + (if array_nth xs i \<in> set (array_to_list ys) then 1 else 0)\<close>
    by (simp add: take_Suc_conv_app_nth)
  moreover have \<open>\<And> j a. j < LENGTH('b) \<Longrightarrow>
      (a \<notin> set (take (Suc j) (array_to_list ys))) = (a \<notin> set (take j (array_to_list ys)) \<and> array_nth ys j \<noteq> a)\<close>
    by (auto simp add: take_Suc_conv_app_nth)
  moreover have \<open>\<And> j. j < LENGTH('b) \<Longrightarrow> array_nth ys j \<in> set (array_to_list ys)\<close>
    by (metis array_to_list_length array_to_list_nth nth_mem)
  moreover note More_Word.unat_lt2p[of la] More_Word.unat_lt2p[of lb]
  ultimately show ?case
    apply crush_base
    subgoal for c_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g. c_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(length (filter (\<lambda>x. x \<in> set (array_to_list ys)) (take i (array_to_list xs))))\<close> and
          BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'
      \<close>)
      subgoal
        by (crush_base simp add: More_Word.unat_of_nat_eq)
      subgoal for i
        apply (crush_base simp add: More_Word.unat_of_nat_eq)
        apply (ucincl_discharge\<open>
          rule_tac
            INV=\<open>\<lambda>_ j. \<Squnion> g. c_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(length (filter (\<lambda>x. x \<in> set (array_to_list ys)) (take i (array_to_list xs))))
                         \<star> \<langle>array_nth xs i \<notin> set (take j (array_to_list ys))\<rangle>\<close> and
            BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close> and
            \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_raw_for_loop_framedI'
        \<close>)
        by (crush_base simp add: More_Word.unat_of_nat_eq)
      done
  done
qed

subsection\<open>Loops without \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close>\<close>

text\<open>The proof of @{thm sum_spec} in \<^theory>\<open>Micro_Rust_Examples.Showcase\<close> leaves \<^term>\<open>BRK\<close> uninstantiated. The following proofs instantiate it with \<^term>\<open>\<langle>False\<rangle>\<close>, or leave it uninstantiated for a \<^verbatim>\<open>while\<close> loop.\<close>

definition count_up :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>count_up n l \<equiv> FunctionBody \<lbrakk>
    let mut x = \<llangle>0 :: 64 word\<rrangle>;
    #[fuel(\<epsilon>\<open>n\<close>)] while (*x < \<llangle>l\<rrangle>) {
      x = *x + 1_u64;
    };
    *x
  \<rbrakk>\<close>

definition count_up_contract :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'b) function_contract\<close> where
  \<open>count_up_contract n l \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l < n\<rangle> in
    let post = \<lambda> r. \<langle>r = l\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma sum_spec_BRK_False:
  shows \<open>\<Gamma>; sum_array nums l \<Turnstile>\<^sub>F sum_array_contract nums l\<close>
proof (crush_boot f: sum_array_def contract: sum_array_contract_def, goal_cases)
  case 1
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow> sum_list (take (Suc i) (array_to_list nums)) = sum_list (take i (array_to_list nums)) + array_nth nums i\<close>
    by (simp add: take_Suc_conv_app_nth)
  moreover note More_Word.unat_lt2p[of l]
  ultimately show ?case
    apply crush_base
    subgoal for sum_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g. sum_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(sum_list (take i (array_to_list nums)))\<close> and
          BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'
      \<close>)
      by (crush_base simp add: More_Word.unat_of_nat_eq)
  done
qed

lemma count_up_spec:
  shows \<open>\<Gamma>; count_up n l \<Turnstile>\<^sub>F count_up_contract n l\<close>
proof (crush_boot f: count_up_def contract: count_up_contract_def, goal_cases)
  case 1
  moreover note count_up_facts[of _ l]
  moreover note More_Word.unat_lt2p[of l]
  ultimately show ?case
    apply crush_base
    subgoal for x_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>j. \<Squnion> g v. x_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>unat v \<le> unat l \<and> (j = 0 \<longrightarrow> unat v = unat l) \<and> (0 < j \<longrightarrow> unat v + j \<ge> n)\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion> g v. x_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>unat v < unat l \<and> unat v + Suc j \<ge> n\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI
      \<close>)
      by crush_base
    done
qed

lemma count_up_spec_BRK_False:
  shows \<open>\<Gamma>; count_up n l \<Turnstile>\<^sub>F count_up_contract n l\<close>
proof (crush_boot f: count_up_def contract: count_up_contract_def, goal_cases)
  case 1
  moreover note count_up_facts[of _ l]
  moreover note More_Word.unat_lt2p[of l]
  ultimately show ?case
    apply crush_base
    subgoal for x_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>j. \<Squnion> g v. x_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>unat v \<le> unat l \<and> (j = 0 \<longrightarrow> unat v = unat l) \<and> (0 < j \<longrightarrow> unat v + j \<ge> n)\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion> g v. x_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>unat v < unat l \<and> unat v + Suc j \<ge> n\<rangle>\<close> and
          BRK=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI
      \<close>)
      by crush_base
    done
qed

end

(*<*)
end
(*>*)
