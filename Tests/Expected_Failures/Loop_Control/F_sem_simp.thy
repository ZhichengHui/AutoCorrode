theory F_sem_simp
  imports Tests.Loop_Control_Semantics
begin
text\<open>As if \<^verbatim>\<open>break 'a\<close> in the inner loop left the outer loop.\<close>
lemma \<open>run (\<lbrakk>
    'a: for i in (\<llangle>[1::nat, 2]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      #[fuel(\<epsilon>\<open>10\<close>)] 'a: loop {
        \<epsilon>\<open>tick 5\<close>;
        break 'a;
      }
      \<epsilon>\<open>tick 6\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 5, 99]\<close>
  by (simp add: run_simps)  (* EXPECTED FAILURE: Failed to finish proof *)
end
