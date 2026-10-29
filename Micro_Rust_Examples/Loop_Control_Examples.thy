(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Loop_Control_Examples
  imports Showcase
begin
(*>*)

section\<open>Loops with \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close>\<close>

text\<open>In the loop rules, a \<^verbatim>\<open>break\<close> caught by the loop establishes the assertion
\<^term>\<open>BRK\<close>, which must entail the postcondition of the loop, and a \<^verbatim>\<open>continue\<close> caught by
the loop establishes the invariant for the next iteration.\<close>

context showcase_ctx
begin

subsection\<open>\<^verbatim>\<open>break\<close>\<close>

definition contains :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>contains nums l k \<equiv> FunctionBody \<lbrakk>
    let mut found = \<llangle>0 :: nat\<rrangle>;
    for i in 0..l {
      if nums[i] == \<llangle>k\<rrangle> {
        found = \<llangle>1 :: nat\<rrangle>;
        break;
      }
    };
    *found
  \<rbrakk>\<close>

definition contains_contract :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>contains_contract nums l k \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l = LENGTH('a)\<rangle> in
    let post = \<lambda> r. \<langle>r \<le> 1 \<and> (r = 1) = (k \<in> set (array_to_list nums))\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma contains_spec:
  shows \<open>\<Gamma>; contains nums l k \<Turnstile>\<^sub>F contains_contract nums l k\<close>
proof (crush_boot f: contains_def contract: contains_contract_def, goal_cases)
  case 1
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow>
      (k \<in> set (take (Suc i) (array_to_list nums))) = (k \<in> set (take i (array_to_list nums)) \<or> array_nth nums i = k)\<close>
    by (auto simp add: take_Suc_conv_app_nth)
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow> array_nth nums i \<in> set (array_to_list nums)\<close>
    by (metis array_to_list_length array_to_list_nth nth_mem)
  moreover note More_Word.unat_lt2p[of l]
  ultimately show ?case
    apply crush_base
    subgoal for found_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g v. found_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>v \<le> 1 \<and> (v = 1) = (k \<in> set (take i (array_to_list nums)))\<rangle>\<close> and
          BRK=\<open>\<lambda>_ _. \<Squnion> g. found_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(1 :: nat) \<star> \<langle>k \<in> set (array_to_list nums)\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'
      \<close>)
      by (crush_base simp add: More_Word.unat_of_nat_eq)
  done
qed

subsection\<open>\<^verbatim>\<open>continue\<close>\<close>

definition sum_except :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>sum_except nums l k \<equiv> FunctionBody \<lbrakk>
    let mut sum = \<llangle>0 :: nat\<rrangle>;
    for i in 0..l {
      let num = nums[i];
      if num == \<llangle>k\<rrangle> {
        continue;
      }
      sum = *sum + num;
    };
    *sum
  \<rbrakk>\<close>

definition sum_except_contract :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>sum_except_contract nums l k \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l = LENGTH('a)\<rangle> in
    let post = \<lambda> r. \<langle>r = sum_list (filter (\<lambda>x. x \<noteq> k) (array_to_list nums))\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma sum_except_spec:
  shows \<open>\<Gamma>; sum_except nums l k \<Turnstile>\<^sub>F sum_except_contract nums l k\<close>
proof (crush_boot f: sum_except_def contract: sum_except_contract_def, goal_cases)
  case 1
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow>
      sum_list (filter (\<lambda>x. x \<noteq> k) (take (Suc i) (array_to_list nums))) =
      sum_list (filter (\<lambda>x. x \<noteq> k) (take i (array_to_list nums))) + (if array_nth nums i = k then 0 else array_nth nums i)\<close>
    by (simp add: take_Suc_conv_app_nth)
  moreover note More_Word.unat_lt2p[of l]
  ultimately show ?case
    apply crush_base
    subgoal for sum_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>_ i. \<Squnion> g. sum_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(sum_list (filter (\<lambda>x. x \<noteq> k) (take i (array_to_list nums))))\<close> and
          BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'
      \<close>)
      by (crush_base simp add: More_Word.unat_of_nat_eq)
  done
qed

end

(*<*)
end
(*>*)
