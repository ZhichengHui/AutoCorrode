theory F_sum_except_spec_false
  imports "Tests.Loop_Control_Examples"
begin

context showcase_ctx
begin

definition sum_except_false_contract :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>sum_except_false_contract nums l k \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l = LENGTH('a)\<rangle> in
    let post = \<lambda> r. \<langle>False\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma sum_except_false_spec:
  shows \<open>\<Gamma>; sum_except nums l k \<Turnstile>\<^sub>F sum_except_false_contract nums l k\<close>
proof (crush_boot f: sum_except_def contract: sum_except_false_contract_def, goal_cases)
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
      by (crush_base simp add: More_Word.unat_of_nat_eq)  (* EXPECTED FAILURE: Failed to finish proof *)
  done
qed

end

end
