theory F_sem_eval
  imports Tests.Loop_Control_Semantics
begin
text\<open>As if the \<^verbatim>\<open>break\<close> in the iterator expression were caught by the inner loop.\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>4\<close>)] loop {
      \<epsilon>\<open>tick 1\<close>;
      for i in (if \<epsilon>\<open>len_eq 3\<close> { break; } else { \<llangle>[3::nat]\<rrangle> }) {
        \<epsilon>\<open>tick i\<close>;
      }
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 3, 1, 1, 3, 99]\<close>
  by eval  (* EXPECTED FAILURE: Failed to apply initial proof method *)
end
