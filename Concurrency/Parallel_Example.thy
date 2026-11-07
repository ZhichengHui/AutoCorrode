(* SPDX-License-Identifier: MIT *)

(*<*)
theory Parallel_Example
  imports Concurrency.Parallel
begin
(*>*)

section\<open>Example: two threads incrementing disjoint cells\<close>

text\<open>A toy machine with two memory cells \<^verbatim>\<open>x\<close> and \<^verbatim>\<open>y\<close>.  A state is a pair of optional integers;
\<^term>\<open>None\<close> means ``this part of the state does not own the cell''.  The separation algebra is
the existing product of two \<^typ>\<open>'a option\<close> algebras: two states are disjoint if they do not both
own the same cell, and \<^verbatim>\<open>+\<close> merges them.  So \<^verbatim>\<open>{(Some a, None)}\<close> is the points-to assertion
``\<^verbatim>\<open>x \<mapsto> a\<close>'' and \<^verbatim>\<open>{(None, Some b)}\<close> is ``\<^verbatim>\<open>y \<mapsto> b\<close>''.\<close>

type_synonym cells = \<open>int option \<times> int option\<close>

text\<open>Reading and writing a cell aborts if the cell is not owned (a ``dangling pointer'').\<close>

definition read_x :: \<open>(cells, int, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>read_x \<equiv> Expression (\<lambda>\<sigma>. case fst \<sigma> of Some v \<Rightarrow> Success v \<sigma> | None \<Rightarrow> Abort DanglingPointer \<sigma>)\<close>

definition write_x :: \<open>int \<Rightarrow> (cells, unit, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>write_x v \<equiv> Expression (\<lambda>\<sigma>. case fst \<sigma> of
     Some _ \<Rightarrow> Success () (Some v, snd \<sigma>) | None \<Rightarrow> Abort DanglingPointer \<sigma>)\<close>

definition read_y :: \<open>(cells, int, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>read_y \<equiv> Expression (\<lambda>\<sigma>. case snd \<sigma> of Some v \<Rightarrow> Success v \<sigma> | None \<Rightarrow> Abort DanglingPointer \<sigma>)\<close>

definition write_y :: \<open>int \<Rightarrow> (cells, unit, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>write_y v \<equiv> Expression (\<lambda>\<sigma>. case snd \<sigma> of
     Some _ \<Rightarrow> Success () (fst \<sigma>, Some v) | None \<Rightarrow> Abort DanglingPointer \<sigma>)\<close>

text\<open>Each thread increments its cell, with a preemption point (\<^term>\<open>pause\<close>) between the read and
the write.  So each thread consists of two atomic steps, and \<^verbatim>\<open>par incr_x incr_y\<close> has several
interleavings, among them the one where both threads read before either writes.  Had both
threads incremented the \<^emph>\<open>same\<close> cell, this interleaving would lose an update; the disjoint
parallel rule cannot be applied to that program because \<^verbatim>\<open>x \<mapsto> a \<star> x \<mapsto> a\<close> is unsatisfiable.\<close>

definition incr_x :: \<open>(cells, unit, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>incr_x \<equiv> bind read_x (\<lambda>v. bind pause (\<lambda>_. write_x (v + 1)))\<close>

definition incr_y :: \<open>(cells, unit, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>incr_y \<equiv> bind read_y (\<lambda>v. bind pause (\<lambda>_. write_y (v + 1)))\<close>

subsection\<open>The separation algebra of two cells\<close>

lemma cells_x_disjoint: \<open>(Some a, None) \<sharp> (\<rho> :: cells) \<longleftrightarrow> fst \<rho> = None\<close>
  by (cases \<rho>) (auto simp add: disjoint_prod_def disjoint_option_def split: option.splits)

lemma cells_x_disjoint': \<open>(\<rho> :: cells) \<sharp> (Some a, None) \<longleftrightarrow> fst \<rho> = None\<close>
  by (cases \<rho>) (auto simp add: disjoint_prod_def disjoint_option_def split: option.splits)

lemma cells_x_plus: \<open>(Some a, None) + (\<rho> :: cells) = (Some a, snd \<rho>)\<close>
  by (cases \<rho>) (simp add: plus_prod_def plus_option_def)

lemma cells_y_disjoint: \<open>(None, Some b) \<sharp> (\<rho> :: cells) \<longleftrightarrow> snd \<rho> = None\<close>
  by (cases \<rho>) (auto simp add: disjoint_prod_def disjoint_option_def split: option.splits)

lemma cells_y_disjoint': \<open>(\<rho> :: cells) \<sharp> (None, Some b) \<longleftrightarrow> snd \<rho> = None\<close>
  by (cases \<rho>) (auto simp add: disjoint_prod_def disjoint_option_def split: option.splits)

lemma cells_y_plus: \<open>(None, Some b) + (\<rho> :: cells) = (fst \<rho>, Some b)\<close>
  by (cases \<rho>) (simp add: plus_prod_def plus_option_def)

lemma cells_sepconj: \<open>{(Some a, None)} \<star> {(None, Some b)} = {(Some a, Some b) :: cells}\<close>
  by (auto simp add: asepconj_def asat_def cells_x_disjoint cells_x_plus cells_x_disjoint')

subsection\<open>The atomic steps of the threads\<close>

lemma evaluate_pause:
  shows \<open>evaluate pause \<sigma> = Yield Pause \<sigma> (\<lambda>_. literal ())\<close>
  by (simp add: pause_def evaluate_def)

lemma evaluate_read_x:
  assumes \<open>fst \<tau> = Some a\<close>
    shows \<open>evaluate read_x \<tau> = Success a \<tau>\<close>
  using assms by (simp add: read_x_def evaluate_def)

lemma evaluate_incr_x:
  assumes \<open>fst \<tau> = Some a\<close>
    shows \<open>evaluate incr_x \<tau> = Yield Pause \<tau> (\<lambda>_. write_x (a + 1))\<close>
  using assms by (simp add: incr_x_def bind_evaluate evaluate_read_x evaluate_pause bind_literal_unit)

lemma atomic_step_incr_x:
  assumes \<open>is_log_transparent_yield_handler y\<close>
      and \<open>fst \<tau> = Some a\<close>
    shows \<open>atomic_step y incr_x \<tau> (c, \<tau>') \<longleftrightarrow> c = Continue (write_x (a + 1)) \<and> \<tau>' = \<tau>\<close>
  using assms
proof -
  have \<open>y Pause \<tau> = {YieldContinue (Ack, \<tau>)}\<close>
    using assms(1) by (cases \<tau>) (simp add: is_log_transparent_yield_handler_def)
  then show ?thesis
    using assms(2) by (auto simp add: atomic_step_def evaluate_incr_x)
qed

lemma atomic_step_write_x:
  assumes \<open>fst \<tau> = Some a\<close>
    shows \<open>atomic_step y (write_x v) \<tau> (c, \<tau>') \<longleftrightarrow> c = Finished () \<and> \<tau>' = (Some v, snd \<tau>)\<close>
  using assms by (auto simp add: atomic_step_def write_x_def evaluate_def)

lemma evaluate_read_y:
  assumes \<open>snd \<tau> = Some b\<close>
    shows \<open>evaluate read_y \<tau> = Success b \<tau>\<close>
  using assms by (simp add: read_y_def evaluate_def)

lemma evaluate_incr_y:
  assumes \<open>snd \<tau> = Some b\<close>
    shows \<open>evaluate incr_y \<tau> = Yield Pause \<tau> (\<lambda>_. write_y (b + 1))\<close>
  using assms by (simp add: incr_y_def bind_evaluate evaluate_read_y evaluate_pause bind_literal_unit)

lemma atomic_step_incr_y:
  assumes \<open>is_log_transparent_yield_handler y\<close>
      and \<open>snd \<tau> = Some b\<close>
    shows \<open>atomic_step y incr_y \<tau> (c, \<tau>') \<longleftrightarrow> c = Continue (write_y (b + 1)) \<and> \<tau>' = \<tau>\<close>
  using assms
proof -
  have \<open>y Pause \<tau> = {YieldContinue (Ack, \<tau>)}\<close>
    using assms(1) by (cases \<tau>) (simp add: is_log_transparent_yield_handler_def)
  then show ?thesis
    using assms(2) by (auto simp add: atomic_step_def evaluate_incr_y)
qed

lemma atomic_step_write_y:
  assumes \<open>snd \<tau> = Some b\<close>
    shows \<open>atomic_step y (write_y v) \<tau> (c, \<tau>') \<longleftrightarrow> c = Finished () \<and> \<tau>' = (fst \<tau>, Some v)\<close>
  using assms by (auto simp add: atomic_step_def write_y_def evaluate_def)

subsection\<open>Thread specifications\<close>

text\<open>Each thread is proven safe by following its two atomic steps.  For each step we show that it
is local (with any frame, which here can only own the other cell, it does the same thing) and
that it leads to the next step or to the post-condition.\<close>

lemma ctriple_incr_x:
  shows \<open>ctriple \<Gamma> {(Some a, None)} incr_x (\<lambda>_. {(Some (a + 1), None)})\<close>
proof -
  have lt: \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
    by simp
  \<comment> \<open>Second step: the write.\<close>
  have w: \<open>safe (yh \<Gamma>) (\<lambda>_. {(Some (a + 1), None)}) (write_x (a + 1)) (Some a, None)\<close>
    by (rule safe.safeI)
       (auto simp add: is_local_def asat_def atomic_step_write_x cells_x_disjoint cells_x_plus
         cells_x_disjoint')
  \<comment> \<open>First step: the read, up to the \<^term>\<open>pause\<close>.\<close>
  have \<open>safe (yh \<Gamma>) (\<lambda>_. {(Some (a + 1), None)}) incr_x (Some a, None)\<close>
    by (rule safe.safeI)
       (use w in \<open>auto simp add: is_local_def asat_def atomic_step_incr_x[OF lt] cells_x_disjoint cells_x_plus
         cells_x_disjoint'\<close>)
  then show ?thesis
    by (simp add: ctriple_def asat_def)
qed

lemma ctriple_incr_y:
  shows \<open>ctriple \<Gamma> {(None, Some b)} incr_y (\<lambda>_. {(None, Some (b + 1))})\<close>
proof -
  have lt: \<open>is_log_transparent_yield_handler (yh \<Gamma>)\<close>
    by simp
  have w: \<open>safe (yh \<Gamma>) (\<lambda>_. {(None, Some (b + 1))}) (write_y (b + 1)) (None, Some b)\<close>
    by (rule safe.safeI)
       (auto simp add: is_local_def asat_def atomic_step_write_y cells_y_disjoint cells_y_plus
         cells_y_disjoint')
  have \<open>safe (yh \<Gamma>) (\<lambda>_. {(None, Some (b + 1))}) incr_y (None, Some b)\<close>
    by (rule safe.safeI)
       (use w in \<open>auto simp add: is_local_def asat_def atomic_step_incr_y[OF lt] cells_y_disjoint cells_y_plus
         cells_y_disjoint'\<close>)
  then show ?thesis
    by (simp add: ctriple_def asat_def)
qed

subsection\<open>The parallel program\<close>

text\<open>By the disjoint parallel rule and adequacy, \<^bold>\<open>every\<close> interleaving of the two threads (for
any valid context \<^verbatim>\<open>\<Gamma>\<close>, i.e. any yield handler that answers \<^term>\<open>NondetOrder\<close> both ways and
ignores \<^term>\<open>Pause\<close>) increments both cells, and the program never aborts.  The statement is the
existing sequential triple \<^verbatim>\<open>sstriple\<close>, i.e. a statement about the existing semantics
\<^term>\<open>deep_evaluates_nondet_basic\<close>.\<close>

theorem sstriple_incr_both:
  shows \<open>\<Gamma> ; {(Some a, Some b)} \<turnstile> par incr_x incr_y \<stileturn>
           (\<lambda>_. {(Some (a + 1), Some (b + 1))}) \<bowtie> \<bottom> \<bowtie> \<bottom>\<close>
proof -
  have \<open>\<Gamma> ; {(Some a, None)} \<star> {(None, Some b)} \<turnstile> par incr_x incr_y \<stileturn>
           (\<lambda>(u, w). {(Some (a + 1), None)} \<star> {(None, Some (b + 1))}) \<bowtie> \<bottom> \<bowtie> \<bottom>\<close>
    by (rule sstriple_par[OF ctriple_incr_x ctriple_incr_y])
  then show ?thesis
    by (rule sstriple_consequence) (auto simp add: cells_sepconj aentails_refl)
qed

(*<*)
end
(*>*)
