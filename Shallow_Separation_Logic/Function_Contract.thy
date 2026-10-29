(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Function_Contract
  imports Triple
begin

subsection\<open>Function contracts\<close>

text\<open>It is sometimes useful to provide independent \<^emph>\<open>contracts\<close> for a function's behaviour which may
not be the most general such behavioural description.  We introduce some dedicated machinery, here,
for working with these contracts:\<close>

datatype_record ('a, 'r, 'abort) function_contract =
  function_contract_pre :: \<open>'a assert\<close> \<comment>\<open>Precondition\<close>
  function_contract_post :: \<open>'r \<Rightarrow> 'a assert\<close> \<comment>\<open>Success post-condition\<close>
  function_contract_abort :: \<open>'abort abort \<Rightarrow> 'a assert\<close> \<comment>\<open>Abort post-condition\<close>

abbreviation \<open>make_function_contract_with_abort \<equiv> make_function_contract\<close>
abbreviation make_function_contract where
  \<open>make_function_contract pre post \<equiv> make_function_contract_with_abort pre post \<bottom>\<close>

(*<*)
context sepalg begin
(*>*)

definition satisfies_function_contract :: \<open>('a, 'abort, 'i, 'o) striple_context \<Rightarrow>
      ('a, 'r, 'abort, 'i prompt, 'o prompt_output) function_body \<Rightarrow>
      ('a, 'r, 'abort) function_contract \<Rightarrow> bool\<close> (\<open>(_)/ ; (_) \<Turnstile>\<^sub>F (_)\<close> [50,50,50]50) where
  \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C> \<longleftrightarrow>
     \<Gamma> ; function_contract_pre \<C>
         \<turnstile> function_body f
         \<stileturn> function_contract_post \<C>
            \<bowtie> function_contract_post \<C>
            \<bowtie> function_contract_abort \<C>\<close>

lemma satisfies_function_contractI:
  assumes \<open>\<Gamma> ; function_contract_pre \<C> \<turnstile> function_body f
                 \<stileturn> function_contract_post \<C> \<bowtie> function_contract_post \<C> \<bowtie> function_contract_abort \<C>\<close>
    shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
  using assms by (simp add: satisfies_function_contract_def)

lemma satisfies_function_contractE:
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
      and \<open>(\<And>\<rho>. \<Gamma> ; function_contract_pre \<C> \<turnstile> call f
                \<stileturn> function_contract_post \<C> \<bowtie> \<rho> \<bowtie> function_contract_abort \<C>) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (cases f) (simp add: satisfies_function_contract_def sstriple_callI)

lemma satisfies_function_contractE':
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
      and \<open>(\<Gamma> ; function_contract_pre \<C> \<turnstile> function_body f
                \<stileturn> function_contract_post \<C> \<bowtie> function_contract_post \<C> \<bowtie> function_contract_abort \<C>) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (cases f) (simp add: satisfies_function_contract_def sstriple_callI)

lemma satisfies_function_contract_tripleD:
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
  shows \<open>\<And>\<rho>. \<Gamma> ; function_contract_pre \<C> \<turnstile> call f
               \<stileturn> function_contract_post \<C> \<bowtie> \<rho> \<bowtie> function_contract_abort \<C>\<close>
using assms by (auto elim: satisfies_function_contractE)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma satisfies_function_contract_tripleD':
  assumes \<open>\<Gamma> ; f \<Turnstile>\<^sub>F \<C>\<close>
  shows \<open>\<Gamma> ; function_contract_pre \<C> \<turnstile> function_body f
               \<stileturn> function_contract_post \<C> \<bowtie> function_contract_post \<C> \<bowtie> function_contract_abort \<C>\<close>
  using assms by (auto elim: satisfies_function_contractE')

lemma function_contract_implies_is_local:
  assumes \<open>\<Gamma>; f \<Turnstile>\<^sub>F \<C>\<close>
  shows \<open>urust_is_local (yh \<Gamma>) (function_body f) (function_contract_pre \<C>)\<close>
  using assms by (elim satisfies_function_contractE', simp add: sstriple_implies_is_local)

text\<open>Weakening rules for contracts are proved in the standard library,
building on the separation logic automation.\<close>

subsection\<open>Recursive functions defined by iterating a step functional\<close>

text\<open>A recursive uRust function is \<^term>\<open>(step ^^ n) P\<close>: a non-recursive step functional
\<open>step\<close> iterated \<open>n\<close> times (the fuel), starting from a function \<open>P\<close> that panics. A contract
indexed by the fuel holds of it when \<open>P\<close> satisfies the contract at fuel \<open>0\<close> (its precondition
is usually false there) and \<open>step\<close> raises the fuel by one, assuming the contract at fuel
\<open>n\<close> for the function it is applied to. The induction hypothesis is a function specification and
can be passed to the automation as such. One lemma per arity of the function. The contract
\<open>\<C>\<close> is applied to the fuel and to the arguments, so unification cannot determine it:
instantiate it explicitly, as in \<open>rule satisfies_function_contract_funpow2[where \<C>=C]\<close>.\<close>

lemma satisfies_function_contract_funpow:
  assumes \<open>\<Gamma>; P \<Turnstile>\<^sub>F \<C> 0\<close>
      and \<open>\<And>n R. \<Gamma>; R \<Turnstile>\<^sub>F \<C> n \<Longrightarrow> \<Gamma>; step R \<Turnstile>\<^sub>F \<C> (Suc n)\<close>
    shows \<open>\<Gamma>; (step ^^ n) P \<Turnstile>\<^sub>F \<C> n\<close>
using assms by (induction n) auto

lemma satisfies_function_contract_funpow1:
  assumes \<open>\<And>x. \<Gamma>; P x \<Turnstile>\<^sub>F \<C> 0 x\<close>
      and \<open>\<And>n R x. (\<And>x. \<Gamma>; R x \<Turnstile>\<^sub>F \<C> n x) \<Longrightarrow> \<Gamma>; step R x \<Turnstile>\<^sub>F \<C> (Suc n) x\<close>
    shows \<open>\<Gamma>; (step ^^ n) P x \<Turnstile>\<^sub>F \<C> n x\<close>
using assms by (induction n arbitrary: x) auto

lemma satisfies_function_contract_funpow2:
  assumes \<open>\<And>x y. \<Gamma>; P x y \<Turnstile>\<^sub>F \<C> 0 x y\<close>
      and \<open>\<And>n R x y. (\<And>x y. \<Gamma>; R x y \<Turnstile>\<^sub>F \<C> n x y) \<Longrightarrow> \<Gamma>; step R x y \<Turnstile>\<^sub>F \<C> (Suc n) x y\<close>
    shows \<open>\<Gamma>; (step ^^ n) P x y \<Turnstile>\<^sub>F \<C> n x y\<close>
using assms by (induction n arbitrary: x y) auto

lemma satisfies_function_contract_funpow3:
  assumes \<open>\<And>x y z. \<Gamma>; P x y z \<Turnstile>\<^sub>F \<C> 0 x y z\<close>
      and \<open>\<And>n R x y z. (\<And>x y z. \<Gamma>; R x y z \<Turnstile>\<^sub>F \<C> n x y z) \<Longrightarrow>
            \<Gamma>; step R x y z \<Turnstile>\<^sub>F \<C> (Suc n) x y z\<close>
    shows \<open>\<Gamma>; (step ^^ n) P x y z \<Turnstile>\<^sub>F \<C> n x y z\<close>
using assms by (induction n arbitrary: x y z) auto

end

text\<open>This contract requires that a function behaves precisely like the first argument (a 'pure'
function), and does so without requiring any state.\<close>
definition lift_pure_to_contract :: \<open>'b \<Rightarrow> ('s::sepalg, 'b, 'c) function_contract\<close> where
  \<open>lift_pure_to_contract pure \<equiv>
    let pre = emp in
    let post = \<lambda> ret. \<langle>ret = pure\<rangle> in
    make_function_contract pre post\<close>

end