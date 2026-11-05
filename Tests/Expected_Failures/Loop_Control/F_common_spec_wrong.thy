theory F_common_spec_wrong
  imports Tests.Loop_Control_Automation
begin

context showcase_ctx
begin

definition common_wrong_contract :: \<open>(nat, 'a::len) array \<Rightarrow> (nat, 'b::len) array \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
    ('s, nat, 'c) function_contract\<close> where
  \<open>common_wrong_contract xs ys la lb \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat la = LENGTH('a) \<and> unat lb = LENGTH('b)\<rangle> in
    let post = \<lambda> r. \<langle>r \<le> 1 \<and> (r = 1) = (set (array_to_list xs) \<inter> set (array_to_list ys) = {})\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma common_spec_wrong:
  shows \<open>\<Gamma>; common xs ys la lb \<Turnstile>\<^sub>F common_wrong_contract xs ys la lb\<close>
proof (crush_boot f: common_def contract: common_wrong_contract_def, goal_cases)
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
        by (crush_base simp add: More_Word.unat_of_nat_eq)  (* EXPECTED FAILURE: Failed to finish proof *)
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

end

end
