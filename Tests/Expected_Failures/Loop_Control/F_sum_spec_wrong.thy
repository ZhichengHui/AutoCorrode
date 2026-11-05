theory F_sum_spec_wrong
  imports Tests.Loop_Control_Automation
begin

context showcase_ctx
begin

definition sum_array_wrong_contract :: \<open>(nat, 'a::len) array \<Rightarrow> 64 word \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>sum_array_wrong_contract nums l \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>unat l = LENGTH('a)\<rangle> in
    let post = \<lambda> r. \<langle>r = sum_list (array_to_list nums) + 1\<rangle> \<star> can_alloc_reference in
    make_function_contract pre post\<close>

lemma sum_spec_wrong:
  shows \<open>\<Gamma>; sum_array nums l \<Turnstile>\<^sub>F sum_array_wrong_contract nums l\<close>
proof (crush_boot f: sum_array_def contract: sum_array_wrong_contract_def, goal_cases)
  case 1
\<comment> \<open>We follow the Isar \<^verbatim>\<open>moreover\<close> .. \<^verbatim>\<open>ultimately\<close> pattern, first gathering required facts.
This first fact relates the partial sums from before and after executing the loop body.\<close>
  moreover have \<open>\<And> i. i < LENGTH('a) \<Longrightarrow> sum_list (take (Suc i) (array_to_list nums)) = sum_list (take i (array_to_list nums)) + array_nth nums i\<close>
    by (simp add: take_Suc_conv_app_nth)
\<comment> \<open>Second fact asserts that \<^term>\<open>l\<close> is bounded (since it is a \<^typ>\<open>64 word\<close>). This boundedness
condition comes arises from using an \<^verbatim>\<open>i \<in> 0..l\<close> to index into \<^term>\<open>nums\<close>.\<close>
  moreover note More_Word.unat_lt2p[of l]
  ultimately show ?case
\<comment> \<open>We can now start the proof. The first call to \<^verbatim>\<open>crush_base\<close> symbolically executes up until
the start of the loop.\<close>
    apply crush_base
\<comment> \<open>Some reference sum has been allocated in the mean time: give it a name with \<^verbatim>\<open>subgoal\<close>,
so that we can reference it in the loop invariant.\<close>
    subgoal for sum_ref
\<comment> \<open>Now, apply the rule for proving for-loops. The \<^verbatim>\<open>INV=\<open>\<lambda> _ i. \<dots>\<close>\<close> states the loop-invariant
that we will use in the proof to verify our specification. The \<^verbatim>\<open>\<tau>=\<dots>\<close> and \<^verbatim>\<open>\<theta>=\<dots>\<close> refer to
conditions for raising exceptions or returning early while inside the loop body. Making these
equal to \<^term>\<open>\<lambda>_. \<langle>False\<rangle>\<close> ensures that raising an exception or returning early is illegal,
like we would expect.\<close>
      apply (ucincl_discharge\<open>
        rule_tac 
          INV=\<open>\<lambda>_ i. \<Squnion> g. sum_ref \<mapsto>\<langle>\<top>\<rangle> g\<down>(sum_list (take i (array_to_list nums)))\<close> and 
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'
      \<close>)
\<comment> \<open>We are left with two subgoals:
- The first subgoal states that our current state entails the loop invariant after 0 iterations,
and that the loop invariant after all iterations entails our postcondition.
- The second subgoal states that executing the loop body is safe, given that the loop invariant
after n iterations holds. Moreover, the loop invariant after (n+1) iterations holds after execution
of the loop body has finished.
In this case, the automation requires one extra simplification rule to be able to finish the proof\<close>
      by (crush_base simp add: More_Word.unat_of_nat_eq)  (* EXPECTED FAILURE: Failed to finish proof *)
  done
qed

end

end
