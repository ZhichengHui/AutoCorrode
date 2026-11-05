theory F_ml_accept_bad
  imports Tests.Loop_Control_Syntax
begin
ML_val\<open>check_accepted \<^context> "\<lbrakk> break; \<rbrakk>"\<close>  (* EXPECTED FAILURE *)
end
