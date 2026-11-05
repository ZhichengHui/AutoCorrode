theory F_count_up_spec_BRK_False_wrong
  imports Tests.Loop_Control_Automation
begin

context showcase_ctx
begin

definition count_up_wrong_contract :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'b) function_contract\<close> where
  \<open>count_up_wrong_contract n l \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l < n\<rangle> in
    let post = \<lambda> r. \<langle>r = l + 1\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma count_up_spec_BRK_False_wrong:
  shows \<open>\<Gamma>; count_up n l \<Turnstile>\<^sub>F count_up_wrong_contract n l\<close>
proof (crush_boot f: count_up_def contract: count_up_wrong_contract_def, goal_cases)
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
      by crush_base  (* EXPECTED FAILURE: Failed to finish proof *)
    done
qed

end

end
