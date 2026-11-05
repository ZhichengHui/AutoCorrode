theory F_ml_reject_wrongmsg
  imports Tests.Loop_Control_Syntax
begin
ML_val\<open>check_rejected \<^context> "uRust: continue outside of a loop" "\<lbrakk> break; \<rbrakk>"\<close>  (* EXPECTED FAILURE *)
end
