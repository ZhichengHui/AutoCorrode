theory F_contains_spec_false
  imports "Tests.Loop_Control_Examples"
begin

context showcase_ctx
begin

definition contains_false_contract :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>contains_false_contract nums l k \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l = LENGTH('a)\<rangle> in
    let post = \<lambda> r. \<langle>False\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma contains_false_spec:
  shows \<open>\<Gamma>; contains nums l k \<Turnstile>\<^sub>F contains_false_contract nums l k\<close>
proof (crush_boot f: contains_def contract: contains_false_contract_def, goal_cases)
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
      by (crush_base simp add: More_Word.unat_of_nat_eq)  (* EXPECTED FAILURE *)
  done
qed

end

end
