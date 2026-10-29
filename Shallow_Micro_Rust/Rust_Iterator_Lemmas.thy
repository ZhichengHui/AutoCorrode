(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Rust_Iterator_Lemmas
  imports Rust_Iterator Core_Expression Core_Expression_Lemmas Core_Syntax Range_Type
begin
(*>*)

section \<open>Inductive definition of loop constructs\<close>

lemma gather'_nil [micro_rust_simps]:
  shows \<open>gather' [] acc = literal acc\<close>
  by (auto simp add: gather'_def foldM_def)

lemma gather'_cons [micro_rust_simps]: 
  shows \<open>gather' (t0 # thunks) acc = bind t0 (\<lambda>v0. gather' thunks (acc @ [v0]))\<close>
  by (auto simp add: gather'_def foldM_def) 

lemma sequence'_nil [micro_rust_simps]:
  shows \<open>sequence' [] = skip\<close>
  by (auto simp add: sequence'_def)

lemma sequence'_cons [micro_rust_simps]: 
  shows \<open>sequence' (e # es) = sequence e (sequence' es)\<close>
  by (auto simp add: sequence'_def) 

lemma raw_for_loop_nil [micro_rust_simps]:
  shows \<open>raw_for_loop lbl [] body = skip\<close>
  by (auto simp add: raw_for_loop_def micro_rust_simps)

lemma raw_for_loop_cons [micro_rust_simps]:
  shows \<open>raw_for_loop lbl (x#xs) body =
           bind (loop_step lbl (sequence (body x) (literal True)))
             (\<lambda>c. if c then raw_for_loop lbl xs body else skip)\<close>
  by (simp add: raw_for_loop_def cong: if_cong)

lemma raw_for_loop_map:
  shows \<open>raw_for_loop lbl (List.map g xs) body = raw_for_loop lbl xs (\<lambda>x. body (g x))\<close>
  by (induction xs) (simp_all add: raw_for_loop_nil raw_for_loop_cons cong: if_cong)

lemma raw_for_loop_upt_nth:
  shows \<open>raw_for_loop lbl [0..<length xs] (\<lambda>i. f (xs ! i)) = raw_for_loop lbl xs f\<close>
proof -
  have \<open>raw_for_loop lbl (List.map ((!) xs) [0..<length xs]) f =
          raw_for_loop lbl [0..<length xs] (\<lambda>i. f (xs ! i))\<close>
    by (rule raw_for_loop_map)
  then show ?thesis
    by (simp only: map_nth)
qed

lemma bounded_while_zero [micro_rust_simps]:
  shows \<open>bounded_while lbl 0 cond body = skip\<close>
  by simp

lemma bounded_while_Suc [micro_rust_simps]:
  shows \<open>bounded_while lbl (Suc n) cond body =
     bind (loop_step lbl (bind cond (\<lambda>c. if c then sequence body (literal True) else literal False)))
       (\<lambda>c. if c then bounded_while lbl n cond body else skip)\<close>
  by simp

\<comment>\<open>Use this to unroll one loop iteration at a time when dealing with a loop with a large
   number of iterations.\<close>
lemma raw_for_loop_standard_unroll_once_simp:
  shows \<open>raw_for_loop lbl (list.map word64_of_nat [n..<m]) body =
         (if n < m then
                   bind (loop_step lbl (sequence (body (word64_of_nat n)) (literal True)))
                     (\<lambda>c. if c then raw_for_loop lbl (list.map word64_of_nat [(Suc n)..<m]) body else skip)
                else
                   skip)\<close>
  by (cases \<open>n < m\<close>) (simp_all add: raw_for_loop_cons raw_for_loop_nil upt_conv_Cons)

lemma urust_sequence_cong:
  assumes \<open>e = e'\<close>
  shows \<open>(e; f) = (e'; f)\<close>
  using assms by simp

lemma urust_loop_step_cong:
  assumes \<open>e = e'\<close>
  shows \<open>bind (loop_step lbl (sequence e (literal True))) f = bind (loop_step lbl (sequence e' (literal True))) f\<close>
  using assms by simp

lemmas raw_for_loop_unroll_once_cong =
  urust_loop_step_cong[where f=\<open>\<lambda>c. if c then raw_for_loop _ _ _ else skip\<close>]

section\<open>Simplification rules for static loops\<close>

lemma iterator_make_iterator_from_list [simp]:
  shows \<open>iterator_ethunks (make_iterator_from_list ls) = List.map literal ls\<close> 
  by (simp add: iterator_ethunks_def make_iterator_from_list_def micro_rust_simps)

lemma iterator_make_iterator_from_range [simp]:
  shows \<open>iterator_ethunks (make_iterator_from_range r) = List.map literal (range_into_list r)\<close> 
  by (simp add: make_iterator_from_range_def)

lemma bind_literal_compose [micro_rust_simps]:
  shows \<open>(\<lambda>e. bind e f) \<circ> literal = f\<close> 
  by (intro ext, simp add:micro_rust_simps)

lemma map_nth' [simp]:
  shows \<open>List.map (\<lambda>i. f (ls ! i)) [0..<length ls] = List.map f ls\<close> 
  apply (induction ls rule: List.rev_induct)
  apply force
  apply clarsimp
  apply (rule map_upt_eqI, force)
  apply (clarsimp simp add: nth_append)
  done

lemma bind_map [micro_rust_simps]:
  shows \<open>list.map (\<lambda>xa. bind (ls ! xa) body) [0..<length ls] = list.map (\<lambda>e. bind e body) ls\<close>
  using map_nth' by fastforce

lemma for_loop_list [micro_rust_simps]:
  fixes body :: \<open>'a \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  shows \<open>for_loop lbl (\<up>(make_iterator_from_list ls)) body = raw_for_loop lbl ls body\<close>
proof -
  let ?t = \<open>List.map literal ls :: ('s, 'a, 'r, 'abort, 'i, 'o) expression list\<close>
  have \<open>for_loop lbl (\<up>(make_iterator_from_list ls)) body =
          raw_for_loop lbl [0..<length ?t] (\<lambda>i. bind (?t ! i) body)\<close>
    by (simp add: for_loop_def for_loop_core_def micro_rust_simps)
  also have \<open>\<dots> = raw_for_loop lbl ?t (\<lambda>e. bind e body)\<close>
    by (rule raw_for_loop_upt_nth)
  also have \<open>\<dots> = raw_for_loop lbl ls (\<lambda>x. bind (literal x) body)\<close>
    by (rule raw_for_loop_map)
  also have \<open>\<dots> = raw_for_loop lbl ls body\<close>
    by (simp add: micro_rust_simps)
  finally show ?thesis .
qed

(*<*)
end
(*>*)
