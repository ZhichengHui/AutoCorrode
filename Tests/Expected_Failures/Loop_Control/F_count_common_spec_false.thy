theory F_count_common_spec_false
  imports Tests.Loop_Control_Automation
begin

context showcase_ctx
begin

definition count_common_false_contract :: \<open>(nat, 'a::len) array \<Rightarrow> (nat, 'b::len) array \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
    ('s, nat, 'c) function_contract\<close> where
  \<open>count_common_false_contract xs ys la lb \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat la = LENGTH('a) \<and> unat lb = LENGTH('b)\<rangle> in
    let post = \<lambda> r. \<langle>False\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma count_common_spec_false:
  shows \<open>\<Gamma>; count_common xs ys la lb \<Turnstile>\<^sub>F count_common_false_contract xs ys la lb\<close>
proof (crush_boot f: count_common_def contract: count_common_false_contract_def, goal_cases)
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
        by (crush_base simp add: More_Word.unat_of_nat_eq)  (* EXPECTED FAILURE *)
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

end

end
