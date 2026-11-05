theory F_count_skip_spec_false
  imports Tests.Loop_Control_Automation
begin

context showcase_ctx
begin

definition count_skip_false_contract :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>count_skip_false_contract n k l \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l < n \<and> 0 < k \<and> k \<le> l\<rangle> in
    let post = \<lambda> r. \<langle>False\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma count_skip_spec_false:
  shows \<open>\<Gamma>; count_skip n k l \<Turnstile>\<^sub>F count_skip_false_contract n k l\<close>
proof (crush_boot f: count_skip_def contract: count_skip_false_contract_def, goal_cases)
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
      by crush_base  (* EXPECTED FAILURE: Failed to finish proof *)
    done
qed

end

end
