theory F_count_to_spec_wrong
  imports Tests.Loop_Control_Automation
begin

context showcase_ctx
begin

definition count_to_wrong_contract :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'b) function_contract\<close> where
  \<open>count_to_wrong_contract n k l \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>k < l \<and> unat k < n\<rangle> in
    let post = \<lambda> r. \<langle>r = l\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma count_to_spec_wrong:
  shows \<open>\<Gamma>; count_to n k l \<Turnstile>\<^sub>F count_to_wrong_contract n k l\<close>
proof (crush_boot f: count_to_def contract: count_to_wrong_contract_def, goal_cases)
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
      done  (* EXPECTED FAILURE: Failed to finish proof *)
    done
qed

end

end
