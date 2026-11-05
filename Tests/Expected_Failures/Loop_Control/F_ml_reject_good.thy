theory F_ml_reject_good
  imports Tests.Loop_Control_Syntax
begin
ML_val\<open>check_rejected \<^context> "uRust: break outside of a loop" "\<lbrakk> #[fuel(\<epsilon>\<open>0\<close>)] loop { break; } \<rbrakk>"\<close>  (* EXPECTED FAILURE: Accepted: *)
end
