theory F_sum_until_spec_wrong
  imports Tests.Loop_Control_Automation
begin

context showcase_ctx
begin

definition sum_until_wrong_contract :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>sum_until_wrong_contract nums l k s \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l = LENGTH('a)\<rangle> in
    let post = \<lambda> r. \<langle>r = sum_list (takeWhile (\<lambda>x. x \<noteq> s) (array_to_list nums))\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma sum_until_spec_wrong:
  shows \<open>\<Gamma>; sum_until nums l k s \<Turnstile>\<^sub>F sum_until_wrong_contract nums l k s\<close>
proof (crush_boot f: sum_until_def contract: sum_until_wrong_contract_def, goal_cases)
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
      by (crush_base simp add: More_Word.unat_of_nat_eq)  (* EXPECTED FAILURE *)
  done
qed

end

end
