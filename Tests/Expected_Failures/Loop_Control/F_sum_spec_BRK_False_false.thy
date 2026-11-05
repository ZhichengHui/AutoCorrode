theory F_sum_spec_BRK_False_false
  imports Tests.Loop_Control_Automation
begin

context showcase_ctx
begin

definition sum_array_false_contract :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>sum_array_false_contract nums l \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l = LENGTH('a)\<rangle> in
    let post = \<lambda> r. \<langle>False\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma sum_spec_BRK_False_false:
  shows \<open>\<Gamma>; sum_array nums l \<Turnstile>\<^sub>F sum_array_false_contract nums l\<close>
proof (crush_boot f: sum_array_def contract: sum_array_false_contract_def, goal_cases)
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
      by (crush_base simp add: More_Word.unat_of_nat_eq)  (* EXPECTED FAILURE *)
  done
qed

end

end
