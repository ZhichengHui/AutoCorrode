(* SPDX-License-Identifier: MIT *)

(*<*)
theory Parallel
  imports Shallow_Separation_Logic.Triple
begin
(*>*)

section\<open>Parallel composition: interleaving semantics and the disjoint parallel rule\<close>

text\<open>This theory is a deliberately minimal first step towards concurrency in AutoCorrode.  It
provides
\begin{enumerate*}
\item an interleaving semantics for the parallel composition \<^verbatim>\<open>par e1 e2\<close> of two \<^verbatim>\<open>\<mu>Rust\<close>
  expressions,
\item a program logic judgement for threads, \<^verbatim>\<open>ctriple\<close>, together with the \<^emph>\<open>disjoint
  parallel rule\<close> of concurrent separation logic (CSL), proven sound, and
\item an adequacy theorem connecting \<^verbatim>\<open>ctriple\<close> to the existing sequential triple
  \<^verbatim>\<open>sstriple\<close>, so that everything is ultimately a statement about the existing semantics.
\end{enumerate*}
A small example is in \<^verbatim>\<open>Parallel_Example.thy\<close>.  Nothing in this theory is axiomatised and
no existing theory is modified.\<close>

subsection\<open>Design overview\<close>

text\<open>\<^bold>\<open>Where can a thread be interrupted?\<close>  A \<^verbatim>\<open>\<mu>Rust\<close> expression is shallowly embedded:
it is (a wrapper around) a HOL function from states to \<^verbatim>\<open>continuation\<close>s.  Applying it to a
state with \<^term>\<open>evaluate\<close> runs it until it either finishes (\<^term>\<open>Success\<close>, \<^term>\<open>Return\<close>,
\<^term>\<open>Abort\<close>) or \<^emph>\<open>yields\<close> to the environment (\<^term>\<open>Yield\<close>), handing over a prompt, the
current state and a continuation.  Between two yields we cannot look inside the HOL function:
there is no notion of ``the next statement'' in a shallow embedding.  Hence the only places
where another thread can sensibly be scheduled are the yields.  This fixes the
\<^bold>\<open>atomicity granularity\<close> of this development:

  \<^emph>\<open>One atomic step of a thread = one call of \<^term>\<open>evaluate\<close>, i.e. the code from one
  yield (or the start) up to the next yield (or the end), followed by the resolution of that
  yield by the yield handler.\<close>

Code without yields therefore runs atomically.  A program can introduce a preemption point
explicitly with \<^term>\<open>pause\<close> (which the standard yield handlers resolve as a no-op).  For a
statement-level interleaving one would make every primitive memory access yield; nothing below
depends on how often a thread yields.

\<^bold>\<open>How is parallel composition defined?\<close>  Instead of a new machine over configurations of
several threads, \<^verbatim>\<open>par e1 e2\<close> is itself an ordinary \<^verbatim>\<open>\<mu>Rust\<close> expression.  It is a
``scheduler written in \<^verbatim>\<open>\<mu>Rust\<close>'': at every scheduling point it yields the existing
prompt \<^term>\<open>NondetOrder\<close>, and the answer \<^term>\<open>NondetLeft\<close>/\<^term>\<open>NondetRight\<close> decides
which thread runs its next atomic step.  Any yield of a thread is forwarded to the environment
and, once answered, leads to the next scheduling point.  All yield handlers in valid triple
contexts answer \<^term>\<open>NondetOrder\<close> with \<^emph>\<open>both\<close> answers (\<^term>\<open>is_nondet_order_yield_handler\<close>), so
the existing set-valued deep evaluation \<^term>\<open>deep_evaluates_nondet_basic\<close> of \<^verbatim>\<open>par e1 e2\<close>
is exactly the set of results of all interleavings.  This has three advantages: no new
evaluator is needed, \<^verbatim>\<open>par\<close> composes with everything else (sequencing, nesting \<^verbatim>\<open>par\<close>s,
calling it from functions), and correctness of \<^verbatim>\<open>par\<close> can be stated with the existing
\<^verbatim>\<open>sstriple\<close>.  Memory is sequentially consistent: there is one global state and each atomic
step reads and writes it directly.

\<^bold>\<open>Why a new judgement for the threads?\<close>  The existing triple \<^verbatim>\<open>sstriple\<close> only speaks about
the \<^emph>\<open>whole\<close> (deep) evaluation of an expression: its locality condition \<^term>\<open>is_local\<close>
says that a frame is untouched at the \<^emph>\<open>end\<close>.  A thread could still modify the frame in an
intermediate step and restore it later; running another thread in between would observe the
modification.  The premises of a parallel rule must thus constrain \<^emph>\<open>every atomic step\<close>.  We
define a safety predicate in the style of Vafeiadis (``Concurrent Separation Logic and
Operational Semantics'', MFPS 2011): \<^verbatim>\<open>safe y Q e \<sigma>\<close> says that each atomic step of \<^verbatim>\<open>e\<close> from the
(thread-local) state \<^verbatim>\<open>\<sigma>\<close> is local, never returns early or aborts, ends in \<^verbatim>\<open>Q\<close> when it
finishes, and leads to safe continuations.  Vafeiadis needs a step index \<^verbatim>\<open>safe\<^sub>n\<close> because
commands may diverge; here every expression has finitely many yields (the expression datatype is
well-founded, cf. \<^term>\<open>expression_wf\<close>), so a plain inductive definition suffices and the
soundness proofs are by rule induction.

\<^bold>\<open>Simplifications\<close> (all deliberate, to be lifted in later work):
\begin{itemize}
\item Only \<^emph>\<open>disjoint\<close> parallelism: no shared resources, no locks, no resource invariants,
  no atomic read-modify-write on shared data, no rely/guarantee.  Threads may not even read
  each other's state.  Adding a resource invariant \<^verbatim>\<open>I\<close> would change \<^verbatim>\<open>safe\<close> so that each
  atomic step may additionally take \<^verbatim>\<open>I\<close> from and give \<^verbatim>\<open>I\<close> back to the environment (exactly
  as in Vafeiadis' paper); \<^verbatim>\<open>atomic\<close> blocks then become yield-free code.
\item Threads must not \<^term>\<open>Return\<close> early or \<^term>\<open>Abort\<close> (the post-conditions for these
  are \<^term>\<open>\<bottom>\<close>).  Operationally, an early return or abort of one thread ends the whole
  \<^verbatim>\<open>par\<close> (and thus kills the other thread); the logic simply proves that this never happens.
  Yields whose handler aborts are included in this: a thread must only yield prompts that the
  handler answers.
\item Partial correctness of the usual shallow kind: every expression terminates by
  construction, so there is no liveness or fairness question.
\item Exactly two threads; more are obtained by nesting \<^verbatim>\<open>par\<close>.  No thread creation
  (\<^verbatim>\<open>spawn\<close>/\<^verbatim>\<open>join\<close>) as separate operations, no thread identifiers, no weak memory.
\end{itemize}\<close>

subsection\<open>Atomic steps\<close>

text\<open>The result of one atomic step: the thread finished with a value, returned early, aborted,
or yielded and will continue with the given expression once it is scheduled again.\<close>

datatype ('s, 'v, 'r, 'abort, 'i, 'o) step_outcome
  = Finished 'v
  | Returned 'r
  | Aborted \<open>'abort abort\<close>
  | Continue \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>

text\<open>One atomic step of \<^verbatim>\<open>e\<close> from state \<^verbatim>\<open>\<sigma>\<close> under the yield handler \<^verbatim>\<open>y\<close>: evaluate up to the
next yield, and let the yield handler answer that yield.  It is written as a relation of the
shape \<^typ>\<open>'s \<Rightarrow> ('t \<times> 's) \<Rightarrow> bool\<close>, the shape that \<^term>\<open>is_local\<close> expects.\<close>

definition atomic_step ::
  \<open>('s, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
     's \<Rightarrow> (('s, 'v, 'r, 'abort, 'i, 'o) step_outcome \<times> 's) \<Rightarrow> bool\<close> where
  \<open>atomic_step y e \<sigma> \<equiv> \<lambda>(c, \<sigma>''). case evaluate e \<sigma> of
       Success v \<sigma>' \<Rightarrow> c = Finished v \<and> \<sigma>'' = \<sigma>'
     | Return r \<sigma>' \<Rightarrow> c = Returned r \<and> \<sigma>'' = \<sigma>'
     | Abort a \<sigma>' \<Rightarrow> c = Aborted a \<and> \<sigma>'' = \<sigma>'
     | Yield \<pi> \<sigma>' k \<Rightarrow> (\<exists>\<omega>. c = Continue (k \<omega>) \<and> YieldContinue (\<omega>, \<sigma>'') \<in> y \<pi> \<sigma>')
                     \<or> (\<exists>a. c = Aborted a \<and> YieldAbort a \<sigma>'' \<in> y \<pi> \<sigma>')\<close>

text\<open>The existing deep evaluation is nothing but the iteration of atomic steps.  This lemma is
the bridge between the step-wise view used by the concurrent logic and the existing semantics.\<close>

lemma deep_evaluates_nondet_basic_atomic_step:
  shows \<open>c \<in> deep_evaluates_nondet_basic y e \<sigma> \<longleftrightarrow>
     (\<exists>v \<sigma>'. atomic_step y e \<sigma> (Finished v, \<sigma>') \<and> c = Success v \<sigma>') \<or>
     (\<exists>r \<sigma>'. atomic_step y e \<sigma> (Returned r, \<sigma>') \<and> c = Return r \<sigma>') \<or>
     (\<exists>a \<sigma>'. atomic_step y e \<sigma> (Aborted a, \<sigma>') \<and> c = Abort a \<sigma>') \<or>
     (\<exists>e' \<sigma>'. atomic_step y e \<sigma> (Continue e', \<sigma>') \<and> c \<in> deep_evaluates_nondet_basic y e' \<sigma>')\<close>
  apply (subst deep_evaluates_nondet_basic.simps)
  apply (cases \<open>evaluate e \<sigma>\<close>; simp add: atomic_step_def)
  apply (auto split: yield_handler_nondet_basic_result.splits prod.splits)
   apply (metis prod.collapse yield_handler_nondet_basic_result.exhaust)
  apply force
  done

subsection\<open>Parallel composition\<close>

text\<open>\<^verbatim>\<open>par e1 e2\<close> first yields \<^term>\<open>NondetOrder\<close> to let the environment (the scheduler) pick a
thread.  The chosen thread performs one atomic step:
\begin{itemize}
\item if it yields a prompt, the prompt is forwarded unchanged to the environment, and after the
  answer we are back at a scheduling point, \<^verbatim>\<open>par\<close> of the two remaining threads;
\item if it finishes with a value, we yield \<^term>\<open>Pause\<close> (a no-op for all valid yield
  handlers) and then run the other thread alone, pairing up the two values.  The \<^term>\<open>Pause\<close>
  keeps the granularity honest: without it, the last step of one thread and the first step of
  the other would be fused into one atomic step, which would hide interleavings from an
  enclosing \<^verbatim>\<open>par\<close>;
\item an early return or abort of a thread ends the whole \<^verbatim>\<open>par\<close>.
\end{itemize}
Termination of the definition follows from the well-foundedness of \<^term>\<open>expression_wf\<close>: each
recursive call is on a continuation of a yield of \<^verbatim>\<open>e1\<close> (with \<^verbatim>\<open>e2\<close> unchanged) or vice versa,
so the pair \<^verbatim>\<open>(e1, e2)\<close> decreases lexicographically.\<close>

function par ::
  \<open>('s, 'v1, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
   ('s, 'v2, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
   ('s, 'v1 \<times> 'v2, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>par e1 e2 = Expression (\<lambda>\<sigma>. Yield NondetOrder \<sigma> (\<lambda>\<omega>.
      if \<omega> = NondetLeft then
        Expression (\<lambda>\<sigma>. case evaluate e1 \<sigma> of
            Success v1 \<sigma>' \<Rightarrow> Yield Pause \<sigma>' (\<lambda>_. bind e2 (\<lambda>v2. literal (v1, v2)))
          | Return r \<sigma>' \<Rightarrow> Return r \<sigma>'
          | Abort a \<sigma>' \<Rightarrow> Abort a \<sigma>'
          | Yield \<pi> \<sigma>' k \<Rightarrow> Yield \<pi> \<sigma>' (\<lambda>\<omega>'. par (k \<omega>') e2))
      else
        Expression (\<lambda>\<sigma>. case evaluate e2 \<sigma> of
            Success v2 \<sigma>' \<Rightarrow> Yield Pause \<sigma>' (\<lambda>_. bind e1 (\<lambda>v1. literal (v1, v2)))
          | Return r \<sigma>' \<Rightarrow> Return r \<sigma>'
          | Abort a \<sigma>' \<Rightarrow> Abort a \<sigma>'
          | Yield \<pi> \<sigma>' k \<Rightarrow> Yield \<pi> \<sigma>' (\<lambda>\<omega>'. par e1 (k \<omega>')))))\<close>
  by pat_completeness auto

termination par
proof (relation \<open>expression_wf <*lex*> expression_wf\<close>)
  show \<open>wf (expression_wf <*lex*> expression_wf)\<close>
    by (intro wf_lex_prod expression_wf_is_wf)
qed (force simp add: expression_wf_def expression_wf_base_def)+

declare par.simps[simp del]

text\<open>For the proofs it is convenient to name the two branches of the scheduler.\<close>

definition par_left ::
  \<open>('s, 'v1, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
   ('s, 'v2, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
   ('s, 'v1 \<times> 'v2, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>par_left e1 e2 \<equiv> Expression (\<lambda>\<sigma>. case evaluate e1 \<sigma> of
            Success v1 \<sigma>' \<Rightarrow> Yield Pause \<sigma>' (\<lambda>_. bind e2 (\<lambda>v2. literal (v1, v2)))
          | Return r \<sigma>' \<Rightarrow> Return r \<sigma>'
          | Abort a \<sigma>' \<Rightarrow> Abort a \<sigma>'
          | Yield \<pi> \<sigma>' k \<Rightarrow> Yield \<pi> \<sigma>' (\<lambda>\<omega>'. par (k \<omega>') e2))\<close>

definition par_right ::
  \<open>('s, 'v1, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
   ('s, 'v2, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
   ('s, 'v1 \<times> 'v2, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close> where
  \<open>par_right e1 e2 \<equiv> Expression (\<lambda>\<sigma>. case evaluate e2 \<sigma> of
            Success v2 \<sigma>' \<Rightarrow> Yield Pause \<sigma>' (\<lambda>_. bind e1 (\<lambda>v1. literal (v1, v2)))
          | Return r \<sigma>' \<Rightarrow> Return r \<sigma>'
          | Abort a \<sigma>' \<Rightarrow> Abort a \<sigma>'
          | Yield \<pi> \<sigma>' k \<Rightarrow> Yield \<pi> \<sigma>' (\<lambda>\<omega>'. par e1 (k \<omega>')))\<close>

lemma evaluate_par:
  shows \<open>evaluate (par e1 e2) \<sigma> =
    Yield NondetOrder \<sigma> (\<lambda>\<omega>. if \<omega> = NondetLeft then par_left e1 e2 else par_right e1 e2)\<close>
  unfolding par_left_def par_right_def by (subst par.simps) (simp add: evaluate_def)

text\<open>The atomic steps of \<^verbatim>\<open>par\<close> and of its two branches, expressed through the atomic steps of
the threads.  The first lemma says that a scheduling point does not change the state and
offers both threads.  The other two say that a step of a branch \<^emph>\<open>is\<close> a step of the chosen
thread, with the outcome re-packaged by the following functions.\<close>

fun lift_left ::
  \<open>('s, 'v2, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
   ('s, 'v1, 'r, 'abort, 'i prompt, 'o prompt_output) step_outcome \<Rightarrow>
   ('s, 'v1 \<times> 'v2, 'r, 'abort, 'i prompt, 'o prompt_output) step_outcome\<close> where
  \<open>lift_left e2 (Finished v1) = Continue (bind e2 (\<lambda>v2. literal (v1, v2)))\<close>
| \<open>lift_left e2 (Returned r) = Returned r\<close>
| \<open>lift_left e2 (Aborted a) = Aborted a\<close>
| \<open>lift_left e2 (Continue e1') = Continue (par e1' e2)\<close>

fun lift_right ::
  \<open>('s, 'v1, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow>
   ('s, 'v2, 'r, 'abort, 'i prompt, 'o prompt_output) step_outcome \<Rightarrow>
   ('s, 'v1 \<times> 'v2, 'r, 'abort, 'i prompt, 'o prompt_output) step_outcome\<close> where
  \<open>lift_right e1 (Finished v2) = Continue (bind e1 (\<lambda>v1. literal (v1, v2)))\<close>
| \<open>lift_right e1 (Returned r) = Returned r\<close>
| \<open>lift_right e1 (Aborted a) = Aborted a\<close>
| \<open>lift_right e1 (Continue e2') = Continue (par e1 e2')\<close>

lemma atomic_step_par:
  assumes \<open>is_nondet_order_yield_handler y\<close>
  shows \<open>atomic_step y (par e1 e2) \<sigma> (c, \<sigma>') \<longleftrightarrow>
           \<sigma>' = \<sigma> \<and> (c = Continue (par_left e1 e2) \<or> c = Continue (par_right e1 e2))\<close>
  using assms by (auto simp add: atomic_step_def evaluate_par is_nondet_order_yield_handler_def)

lemma atomic_step_par_left:
  assumes \<open>is_log_transparent_yield_handler y\<close>
  shows \<open>atomic_step y (par_left e1 e2) \<sigma> (c, \<sigma>') \<longleftrightarrow>
           (\<exists>c1. c = lift_left e2 c1 \<and> atomic_step y e1 \<sigma> (c1, \<sigma>'))\<close>
  using assms
  apply (cases \<open>evaluate e1 \<sigma>\<close>)
     apply (auto simp add: atomic_step_def par_left_def evaluate_def is_log_transparent_yield_handler_def)
   apply (metis lift_left.simps(4))
  apply (metis lift_left.simps(3))
  done

lemma atomic_step_par_right:
  assumes \<open>is_log_transparent_yield_handler y\<close>
  shows \<open>atomic_step y (par_right e1 e2) \<sigma> (c, \<sigma>') \<longleftrightarrow>
           (\<exists>c2. c = lift_right e1 c2 \<and> atomic_step y e2 \<sigma> (c2, \<sigma>'))\<close>
  using assms
  apply (cases \<open>evaluate e2 \<sigma>\<close>)
     apply (auto simp add: atomic_step_def par_right_def evaluate_def is_log_transparent_yield_handler_def)
   apply (metis lift_right.simps(4))
  apply (metis lift_right.simps(3))
  done

text\<open>Similarly, a thread that is left alone after its sibling finished (\<^verbatim>\<open>bind e (\<lambda>v. literal
(g v))\<close>) takes exactly the steps of \<^verbatim>\<open>e\<close>, with the final value mapped by \<^verbatim>\<open>g\<close>.\<close>

fun lift_map ::
  \<open>('v \<Rightarrow> 'w) \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) step_outcome \<Rightarrow> ('s, 'w, 'r, 'abort, 'i, 'o) step_outcome\<close> where
  \<open>lift_map g (Finished v) = Finished (g v)\<close>
| \<open>lift_map g (Returned r) = Returned r\<close>
| \<open>lift_map g (Aborted a) = Aborted a\<close>
| \<open>lift_map g (Continue e') = Continue (bind e' (\<lambda>v. literal (g v)))\<close>

lemma atomic_step_bind_literal:
  shows \<open>atomic_step y (bind e (\<lambda>v. literal (g v))) \<sigma> (c, \<sigma>') \<longleftrightarrow>
           (\<exists>c0. c = lift_map g c0 \<and> atomic_step y e \<sigma> (c0, \<sigma>'))\<close>
  apply (cases \<open>evaluate e \<sigma>\<close>)
     apply (auto simp add: atomic_step_def bind_evaluate evaluate_literal)
   apply (metis lift_map.simps(4))
  apply (metis lift_map.simps(3))
  done

subsection\<open>Locality of a single step\<close>

(*<*)
context sepalg begin
(*>*)

text\<open>We reuse the existing notion of locality \<^term>\<open>is_local\<close>, instantiated with the singleton
assertion \<^verbatim>\<open>{\<sigma>}\<close>: \<^verbatim>\<open>is_local R {\<sigma>}\<close> says that running \<^verbatim>\<open>R\<close> on \<^verbatim>\<open>\<sigma>\<close> extended by any compatible frame
gives exactly the results on \<^verbatim>\<open>\<sigma>\<close>, extended by the same, untouched frame.  The following
facts are the whole ``frame algebra'' needed for the parallel rule.\<close>

lemma apart_plus_split:
  assumes \<open>x \<sharp> y + z\<close>
      and \<open>y \<sharp> z\<close>
    shows \<open>x \<sharp> y\<close> and \<open>x \<sharp> z\<close>
proof -
  show \<open>x \<sharp> y\<close>
    using assms sepalg_apart_plus2 by blast
  from assms have \<open>x \<sharp> z + y\<close>
    by (simp add: sepalg_comm)
  moreover from assms have \<open>z \<sharp> y\<close>
    by simp
  ultimately show \<open>x \<sharp> z\<close>
    using sepalg_apart_plus2 by blast
qed

lemma is_local_singletonD:
  assumes \<open>is_local R {\<sigma>}\<close>
      and \<open>\<sigma> \<sharp> \<rho>\<close>
    shows is_local_singleton_apart: \<open>R \<sigma> (c, \<sigma>') \<Longrightarrow> \<sigma>' \<sharp> \<rho>\<close>
      and is_local_singleton_frame: \<open>R (\<sigma> + \<rho>) (c, \<tau>) \<longleftrightarrow> (\<exists>\<sigma>'. R \<sigma> (c, \<sigma>') \<and> \<tau> = \<sigma>' + \<rho>)\<close>
  using assms by (auto simp add: is_local_def asat_def simp del: disjoint_sym)

lemma is_local_frame_step:
  assumes \<open>is_local R {\<sigma>}\<close>
      and \<open>\<sigma> \<sharp> \<rho>\<close>
      and \<open>R (\<sigma> + \<rho>) (c, \<tau>)\<close>
    shows \<open>\<exists>\<sigma>'. R \<sigma> (c, \<sigma>') \<and> \<sigma>' \<sharp> \<rho> \<and> \<tau> = \<sigma>' + \<rho>\<close>
proof -
  from assms(3) obtain \<sigma>' where \<open>R \<sigma> (c, \<sigma>')\<close> \<open>\<tau> = \<sigma>' + \<rho>\<close>
    unfolding is_local_singleton_frame[OF assms(1,2)] by blast
  moreover from this have \<open>\<sigma>' \<sharp> \<rho>\<close>
    using is_local_singleton_apart[OF assms(1,2)] by blast
  ultimately show ?thesis
    by blast
qed

text\<open>Locality is preserved by enlarging the state with something disjoint: this is how a
thread's step, local to its own resources, becomes a step on the whole shared state.  The
proof is plain associativity/commutativity reasoning in the separation algebra.\<close>

lemma is_local_singleton_extend:
  assumes loc: \<open>is_local R {\<sigma>}\<close>
      and sr: \<open>\<sigma> \<sharp> \<rho>\<close>
    shows \<open>is_local R {\<sigma> + \<rho>}\<close>
proof -
  { fix u
    assume sru0: \<open>\<sigma> + \<rho> \<sharp> u\<close>
    have ru: \<open>\<rho> \<sharp> u\<close>
      using sru0 sr sepalg_apart_plus by blast
    have sru: \<open>\<sigma> \<sharp> \<rho> + u\<close>
      using sru0 sr sepalg_apart_assoc by blast
    have su: \<open>\<sigma> \<sharp> u\<close>
      using apart_plus_split(2)[OF sru ru] .
    have assoc: \<open>\<sigma> + \<rho> + u = \<sigma> + (\<rho> + u)\<close>
      using sepalg_assoc[OF sr ru su] by (rule sym)
    have \<open>(\<forall>c s'. R (\<sigma> + \<rho>) (c, s') \<longrightarrow> s' \<sharp> u) \<and>
          (\<forall>c s'. R (\<sigma> + \<rho> + u) (c, s') \<longleftrightarrow> (\<exists>s0'. R (\<sigma> + \<rho>) (c, s0') \<and> s' = s0' + u))\<close>
    proof (intro conjI allI impI)
      fix c s'
      assume \<open>R (\<sigma> + \<rho>) (c, s')\<close>
      then obtain \<sigma>' where \<sigma>': \<open>R \<sigma> (c, \<sigma>')\<close> \<open>s' = \<sigma>' + \<rho>\<close>
        unfolding is_local_singleton_frame[OF loc sr] by blast
      have \<open>\<sigma>' \<sharp> \<rho> + u\<close>
        using is_local_singleton_apart[OF loc sru \<sigma>'(1)] .
      then show \<open>s' \<sharp> u\<close>
        using \<sigma>'(2) ru sepalg_apart_assoc2 by blast
    next
      fix c s'
      show \<open>R (\<sigma> + \<rho> + u) (c, s') \<longleftrightarrow> (\<exists>s0'. R (\<sigma> + \<rho>) (c, s0') \<and> s' = s0' + u)\<close>
      proof
        assume \<open>R (\<sigma> + \<rho> + u) (c, s')\<close>
        then obtain \<sigma>' where \<sigma>': \<open>R \<sigma> (c, \<sigma>')\<close> \<open>s' = \<sigma>' + (\<rho> + u)\<close>
          unfolding assoc is_local_singleton_frame[OF loc sru] by blast
        have \<open>\<sigma>' \<sharp> \<rho> + u\<close>
          using is_local_singleton_apart[OF loc sru \<sigma>'(1)] .
        then have \<open>\<sigma>' \<sharp> \<rho>\<close> \<open>\<sigma>' \<sharp> u\<close>
          using apart_plus_split ru by blast+
        then have \<open>s' = (\<sigma>' + \<rho>) + u\<close>
          using \<sigma>'(2) ru by (simp only: sepalg_assoc)
        moreover have \<open>R (\<sigma> + \<rho>) (c, \<sigma>' + \<rho>)\<close>
          using is_local_singleton_frame[OF loc sr] \<sigma>'(1) by blast
        ultimately show \<open>\<exists>s0'. R (\<sigma> + \<rho>) (c, s0') \<and> s' = s0' + u\<close>
          by blast
      next
        assume \<open>\<exists>s0'. R (\<sigma> + \<rho>) (c, s0') \<and> s' = s0' + u\<close>
        then obtain s0' where s0': \<open>R (\<sigma> + \<rho>) (c, s0')\<close> \<open>s' = s0' + u\<close>
          by blast
        from s0'(1) obtain \<sigma>' where \<sigma>'0: \<open>R \<sigma> (c, \<sigma>')\<close> \<open>s0' = \<sigma>' + \<rho>\<close>
          unfolding is_local_singleton_frame[OF loc sr] by blast
        with s0'(2) have \<sigma>': \<open>R \<sigma> (c, \<sigma>')\<close> \<open>s' = (\<sigma>' + \<rho>) + u\<close>
          by simp_all
        have \<open>\<sigma>' \<sharp> \<rho> + u\<close>
          using is_local_singleton_apart[OF loc sru \<sigma>'(1)] .
        then have \<open>\<sigma>' \<sharp> \<rho>\<close> \<open>\<sigma>' \<sharp> u\<close>
          using apart_plus_split ru by blast+
        then have \<open>s' = \<sigma>' + (\<rho> + u)\<close>
          using \<sigma>'(2) ru by (simp only: sepalg_assoc)
        then show \<open>R (\<sigma> + \<rho> + u) (c, s')\<close>
          using is_local_singleton_frame[OF loc sru] \<sigma>'(1) unfolding assoc by blast
      qed
    qed }
  then show ?thesis
    unfolding is_local_def asat_def by (simp only: singleton_iff) blast
qed

text\<open>Locality is also preserved by re-packaging the outcomes of a relation, which is what
\<^term>\<open>lift_left\<close>, \<^term>\<open>lift_right\<close> and \<^term>\<open>lift_map\<close> do.\<close>

lemma is_local_lift:
  assumes \<open>is_local R \<phi>\<close>
      and \<open>\<And>s c s'. R' s (c, s') \<longleftrightarrow> (\<exists>c0. c = F c0 \<and> R s (c0, s'))\<close>
    shows \<open>is_local R' \<phi>\<close>
  using assms(1) by (simp add: assms(2) is_local_def) blast

subsection\<open>Safety: the step-wise meaning of a thread specification\<close>

text\<open>Technical note: \<^verbatim>\<open>sepalg_comm\<close> is a conditional, permutative simp rule; it reorders
sums \<^verbatim>\<open>\<sigma> + \<rho>\<close> in some facts but not in others (e.g. not under binders), which gets in the way of
the frame bookkeeping below.  We disable it for the proofs below, use it explicitly, and re-enable it at the end of the
theory.\<close>

declare sepalg_comm[simp del]

text\<open>\<^verbatim>\<open>safe y Q e \<sigma>\<close>: the thread \<^verbatim>\<open>e\<close>, owning exactly the resource \<^verbatim>\<open>\<sigma>\<close>, can run in any
environment that does not touch \<^verbatim>\<open>\<sigma>\<close>, and ends in a state satisfying \<^verbatim>\<open>Q\<close>.  Concretely, its next
atomic step from \<^verbatim>\<open>\<sigma>\<close>
\begin{enumerate*}
\item is local (it neither reads nor writes any frame, and behaves identically in the presence of
  any frame),
\item satisfies \<^verbatim>\<open>Q\<close> if it finishes,
\item never returns early and never aborts, and
\item leads to a safe continuation if it yields.
\end{enumerate*}
Compared to Vafeiadis' \<^verbatim>\<open>safe\<^sub>n(C, h, Q)\<close> there is no step index (all executions are finite,
so we take the least fixed point) and no resource invariant (disjoint parallelism only).
Clause (1) uses the existing \<^term>\<open>is_local\<close>, so ``local'' means the same here as in the
sequential logic, only applied to each step instead of to the whole execution.  Note that
the environment's steps never appear in the definition: because each step is local, the
environment can only change state outside \<^verbatim>\<open>\<sigma>\<close>, and \<^verbatim>\<open>safe\<close> is a statement about \<^verbatim>\<open>\<sigma>\<close> alone.\<close>

inductive safe :: \<open>('a, 'abort, 'i, 'o) yield_handler_nondet_basic \<Rightarrow> ('v \<Rightarrow> 'a assert) \<Rightarrow>
    ('a, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow> 'a \<Rightarrow> bool\<close>
  for y Q where
  safeI: \<open>safe y Q e \<sigma>\<close>
    if \<open>is_local (atomic_step y e) {\<sigma>}\<close>
       \<open>\<And>v \<sigma>'. atomic_step y e \<sigma> (Finished v, \<sigma>') \<Longrightarrow> \<sigma>' \<Turnstile> Q v\<close>
       \<open>\<And>r \<sigma>'. \<not> atomic_step y e \<sigma> (Returned r, \<sigma>')\<close>
       \<open>\<And>a \<sigma>'. \<not> atomic_step y e \<sigma> (Aborted a, \<sigma>')\<close>
       \<open>\<And>e' \<sigma>'. atomic_step y e \<sigma> (Continue e', \<sigma>') \<Longrightarrow> safe y Q e' \<sigma>'\<close>

text\<open>The concurrent triple: every state satisfying the precondition is safe.  It uses the same
context type \<^typ>\<open>('a, 'abort, 'i, 'o) striple_context\<close> as \<^verbatim>\<open>sstriple\<close>, so the yield handler
is guaranteed to treat \<^term>\<open>Pause\<close> as a no-op and to offer both answers to
\<^term>\<open>NondetOrder\<close>; this is all that the parallel rule needs to know about the scheduler.\<close>

definition ctriple :: \<open>('a, 'abort, 'i, 'o) striple_context \<Rightarrow> 'a assert \<Rightarrow>
    ('a, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression \<Rightarrow> ('v \<Rightarrow> 'a assert) \<Rightarrow> bool\<close> where
  \<open>ctriple \<Gamma> P e Q \<equiv> \<forall>\<sigma>. \<sigma> \<Turnstile> P \<longrightarrow> safe (yh \<Gamma>) Q e \<sigma>\<close>

subsection\<open>Transferring safety along re-packaged steps\<close>

text\<open>All three uses below (a thread running alone after its sibling finished, and the two
branches of the scheduler) have the same structure: the atomic steps of a new expression
\<^verbatim>\<open>e'\<close> are the steps of a safe thread \<^verbatim>\<open>e\<close>, run in the presence of an extra disjoint resource \<^verbatim>\<open>\<rho>\<close>
(the other thread's state), with outcomes re-packaged by some \<^verbatim>\<open>F\<close>.  The following lemma does
the bookkeeping once: locality comes from \<^term>\<open>is_local_singleton_extend\<close> and
\<^term>\<open>is_local_lift\<close>; every step from the big state \<^verbatim>\<open>\<sigma> + \<rho>\<close> is, by locality, a step from \<^verbatim>\<open>\<sigma>\<close>
with \<^verbatim>\<open>\<rho>\<close> untouched; so the remaining obligations can be stated about the small state.\<close>

lemma safe_lift_step:
  assumes loc: \<open>is_local (atomic_step y e) {\<sigma>}\<close>
      and sr: \<open>\<sigma> \<sharp> \<rho>\<close>
      and step_eq: \<open>\<And>s c s'. atomic_step y e' s (c, s') \<longleftrightarrow> (\<exists>c0. c = F c0 \<and> atomic_step y e s (c0, s'))\<close>
      and no_ret: \<open>\<And>r \<sigma>'. \<not> atomic_step y e \<sigma> (Returned r, \<sigma>')\<close>
      and no_abort: \<open>\<And>a \<sigma>'. \<not> atomic_step y e \<sigma> (Aborted a, \<sigma>')\<close>
      and F_ret: \<open>\<And>c0 r. F c0 = Returned r \<Longrightarrow> \<exists>r'. c0 = Returned r'\<close>
      and F_abort: \<open>\<And>c0 a. F c0 = Aborted a \<Longrightarrow> \<exists>a'. c0 = Aborted a'\<close>
      and fin: \<open>\<And>c0 v \<sigma>'. F c0 = Finished v \<Longrightarrow> atomic_step y e \<sigma> (c0, \<sigma>') \<Longrightarrow> \<sigma>' \<sharp> \<rho> \<Longrightarrow>
                  \<sigma>' + \<rho> \<Turnstile> Q' v\<close>
      and cont: \<open>\<And>c0 e'' \<sigma>'. F c0 = Continue e'' \<Longrightarrow> atomic_step y e \<sigma> (c0, \<sigma>') \<Longrightarrow> \<sigma>' \<sharp> \<rho> \<Longrightarrow>
                  safe y Q' e'' (\<sigma>' + \<rho>)\<close>
    shows \<open>safe y Q' e' (\<sigma> + \<rho>)\<close>
proof -
  \<comment> \<open>Every step of \<^verbatim>\<open>e'\<close> from the big state is a re-packaged step of \<^verbatim>\<open>e\<close> from the small one.\<close>
  have big: \<open>\<exists>c0 \<sigma>'. c = F c0 \<and> atomic_step y e \<sigma> (c0, \<sigma>') \<and> \<sigma>' \<sharp> \<rho> \<and> \<tau> = \<sigma>' + \<rho>\<close>
    if \<open>atomic_step y e' (\<sigma> + \<rho>) (c, \<tau>)\<close> for c \<tau>
    using that is_local_frame_step[OF loc sr] unfolding step_eq by blast
  show ?thesis
  proof (rule safeI)
    show \<open>is_local (atomic_step y e') {\<sigma> + \<rho>}\<close>
      using is_local_lift[OF is_local_singleton_extend[OF loc sr] step_eq] .
  next
    fix v \<tau> assume \<open>atomic_step y e' (\<sigma> + \<rho>) (Finished v, \<tau>)\<close>
    then show \<open>\<tau> \<Turnstile> Q' v\<close>
      using big fin by metis
  next
    fix r \<tau> show \<open>\<not> atomic_step y e' (\<sigma> + \<rho>) (Returned r, \<tau>)\<close>
      using big F_ret no_ret by metis
  next
    fix a \<tau> show \<open>\<not> atomic_step y e' (\<sigma> + \<rho>) (Aborted a, \<tau>)\<close>
      using big F_abort no_abort by metis
  next
    fix e'' \<tau> assume \<open>atomic_step y e' (\<sigma> + \<rho>) (Continue e'', \<tau>)\<close>
    then show \<open>safe y Q' e'' \<tau>\<close>
      using big cont by metis
  qed
qed

text\<open>A safe thread stays safe when it runs next to a disjoint resource \<^verbatim>\<open>\<rho>\<close> that nobody touches,
and its result is post-processed by a pure function \<^verbatim>\<open>g\<close>.  This covers the phase of \<^verbatim>\<open>par\<close>
in which one thread has already finished (its final state is \<^verbatim>\<open>\<rho>\<close>), and also gives the frame
rule for \<^verbatim>\<open>ctriple\<close> below.\<close>

lemma safe_bind_literal:
  assumes \<open>safe y Q e \<sigma>\<close>
      and \<open>\<sigma> \<sharp> \<rho>\<close>
      and post: \<open>\<And>v s. s \<Turnstile> Q v \<Longrightarrow> s \<sharp> \<rho> \<Longrightarrow> s + \<rho> \<Turnstile> Q' (g v)\<close>
    shows \<open>safe y Q' (bind e (\<lambda>v. literal (g v))) (\<sigma> + \<rho>)\<close>
  using assms(1,2)
proof (induction rule: safe.induct)
  case (safeI e \<sigma>)
  show ?case
  proof (rule safe_lift_step[where F=\<open>lift_map g\<close>])
    show \<open>is_local (atomic_step y e) {\<sigma>}\<close> \<open>\<sigma> \<sharp> \<rho>\<close>
      using safeI by auto
    show \<open>\<And>r \<sigma>'. \<not> atomic_step y e \<sigma> (Returned r, \<sigma>')\<close> \<open>\<And>a \<sigma>'. \<not> atomic_step y e \<sigma> (Aborted a, \<sigma>')\<close>
      using safeI by auto
  next
    fix c0 v \<sigma>'
    assume \<open>lift_map g c0 = Finished v\<close> \<open>atomic_step y e \<sigma> (c0, \<sigma>')\<close> \<open>\<sigma>' \<sharp> \<rho>\<close>
    then show \<open>\<sigma>' + \<rho> \<Turnstile> Q' v\<close>
      using safeI post by (cases c0) auto
  next
    fix c0 e'' \<sigma>'
    assume \<open>lift_map g c0 = Continue e''\<close> \<open>atomic_step y e \<sigma> (c0, \<sigma>')\<close> \<open>\<sigma>' \<sharp> \<rho>\<close>
    then show \<open>safe y Q' e'' (\<sigma>' + \<rho>)\<close>
      using safeI by (cases c0) auto
  qed (auto simp add: atomic_step_bind_literal elim: lift_map.elims)
qed

subsection\<open>Soundness of the disjoint parallel rule\<close>

text\<open>A scheduling point does not touch the state, so it is trivially local.\<close>

lemma is_local_par:
  assumes \<open>is_nondet_order_yield_handler y\<close>
    shows \<open>is_local (atomic_step y (par e1 e2)) \<phi>\<close>
  by (auto simp add: is_local_def atomic_step_par[OF assms])

text\<open>The heart of the soundness proof.  If thread 1 is safe on \<^verbatim>\<open>\<sigma>1\<close> and thread 2 is safe on the
disjoint \<^verbatim>\<open>\<sigma>2\<close>, then \<^verbatim>\<open>par e1 e2\<close> is safe on \<^verbatim>\<open>\<sigma>1 + \<sigma>2\<close>.  The proof is a nested rule induction,
first on the safety of \<^verbatim>\<open>e1\<close>, then on the safety of \<^verbatim>\<open>e2\<close>: whichever thread is scheduled makes a
step on the joint state; by locality this is a step on its own part only, leaving the other
part untouched, after which we are again in the situation of the lemma, with a smaller thread
(use the induction hypothesis) or with one thread finished (use \<^term>\<open>safe_bind_literal\<close>).
This is exactly where locality of \<^emph>\<open>every\<close> step is needed: the untouched part is what the
other thread is about to run on.\<close>

lemma safe_par:
  assumes y: \<open>is_nondet_order_yield_handler y\<close> \<open>is_log_transparent_yield_handler y\<close>
      and \<open>safe y Q1 e1 \<sigma>1\<close>
      and \<open>safe y Q2 e2 \<sigma>2\<close>
      and \<open>\<sigma>1 \<sharp> \<sigma>2\<close>
    shows \<open>safe y (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) (par e1 e2) (\<sigma>1 + \<sigma>2)\<close>
  using assms(3-5)
proof (induction arbitrary: e2 \<sigma>2 rule: safe.induct)
  case (safeI e1 \<sigma>1)
  note loc1 = safeI.hyps(1) and fin1 = safeI.hyps(2) and ret1 = safeI.hyps(3)
   and abort1 = safeI.hyps(4) and IH1 = safeI.IH
  have safe1: \<open>safe y Q1 e1 \<sigma>1\<close>
    using safeI.hyps by (blast intro: safe.safeI)
  from safeI.prems show ?case
  proof (induction rule: safe.induct)
    case (safeI e2 \<sigma>2)
    note loc2 = safeI.hyps(1) and fin2 = safeI.hyps(2) and ret2 = safeI.hyps(3)
     and abort2 = safeI.hyps(4) and IH2 = safeI.IH
    have safe2: \<open>safe y Q2 e2 \<sigma>2\<close>
      using safeI.hyps by (blast intro: safe.safeI)
    have sep: \<open>\<sigma>1 \<sharp> \<sigma>2\<close> \<open>\<sigma>2 \<sharp> \<sigma>1\<close> and comm: \<open>\<sigma>2 + \<sigma>1 = \<sigma>1 + \<sigma>2\<close>
      using safeI.prems by (auto simp add: sepalg_comm)
    \<comment> \<open>Thread 1 is scheduled.\<close>
    have left: \<open>safe y (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) (par_left e1 e2) (\<sigma>1 + \<sigma>2)\<close>
    proof (rule safe_lift_step[OF loc1 sep(1) atomic_step_par_left[OF y(2)] ret1 abort1])
      fix c0 e'' \<sigma>1'
      assume F: \<open>lift_left e2 c0 = Continue e''\<close> and st: \<open>atomic_step y e1 \<sigma>1 (c0, \<sigma>1')\<close>
         and sep': \<open>\<sigma>1' \<sharp> \<sigma>2\<close>
      show \<open>safe y (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) e'' (\<sigma>1' + \<sigma>2)\<close>
      proof (cases c0)
        case (Finished v1)
        \<comment> \<open>Thread 1 has finished; thread 2 continues alone next to thread 1's final state.\<close>
        then have \<open>\<sigma>1' \<Turnstile> Q1 v1\<close> and e'': \<open>e'' = bind e2 (\<lambda>v2. literal (v1, v2))\<close>
          using fin1 st F by auto
        moreover have \<open>s + \<sigma>1' \<Turnstile> (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) (v1, v2)\<close>
          if \<open>s \<Turnstile> Q2 v2\<close> \<open>s \<sharp> \<sigma>1'\<close> for v2 s
          using that \<open>\<sigma>1' \<Turnstile> Q1 v1\<close> by (auto intro!: asepconjI simp add: sepalg_comm)
        moreover have \<open>\<sigma>2 \<sharp> \<sigma>1'\<close>
          using sep' by simp
        ultimately have \<open>safe y (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) e'' (\<sigma>2 + \<sigma>1')\<close>
          using safe_bind_literal[OF safe2, where g=\<open>\<lambda>v2. (v1, v2)\<close>] by blast
        then show ?thesis
          using sep' by (simp add: sepalg_comm)
      next
        case (Continue e1')
        then show ?thesis
          using IH1 st F safe2 sep' by auto
      qed (use F in auto)
    qed (auto elim: lift_left.elims)
    \<comment> \<open>Thread 2 is scheduled: symmetric, with the roles of the two parts of the state swapped.\<close>
    have right: \<open>safe y (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) (par_right e1 e2) (\<sigma>2 + \<sigma>1)\<close>
    proof (rule safe_lift_step[OF loc2 sep(2) atomic_step_par_right[OF y(2)] ret2 abort2])
      fix c0 e'' \<sigma>2'
      assume F: \<open>lift_right e1 c0 = Continue e''\<close> and st: \<open>atomic_step y e2 \<sigma>2 (c0, \<sigma>2')\<close>
         and sep': \<open>\<sigma>2' \<sharp> \<sigma>1\<close>
      show \<open>safe y (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) e'' (\<sigma>2' + \<sigma>1)\<close>
      proof (cases c0)
        case (Finished v2)
        then have \<open>\<sigma>2' \<Turnstile> Q2 v2\<close> and e'': \<open>e'' = bind e1 (\<lambda>v1. literal (v1, v2))\<close>
          using fin2 st F by auto
        moreover have \<open>s + \<sigma>2' \<Turnstile> (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) (v1, v2)\<close>
          if \<open>s \<Turnstile> Q1 v1\<close> \<open>s \<sharp> \<sigma>2'\<close> for v1 s
          using that \<open>\<sigma>2' \<Turnstile> Q2 v2\<close> by (auto intro!: asepconjI)
        moreover have \<open>\<sigma>1 \<sharp> \<sigma>2'\<close>
          using sep' by simp
        ultimately have \<open>safe y (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) e'' (\<sigma>1 + \<sigma>2')\<close>
          using safe_bind_literal[OF safe1, where g=\<open>\<lambda>v1. (v1, v2)\<close>] by blast
        then show ?thesis
          using sep' by (simp add: sepalg_comm)
      next
        case (Continue e2')
        moreover have \<open>\<sigma>1 \<sharp> \<sigma>2'\<close>
          using sep' by simp
        ultimately have \<open>safe y (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) e'' (\<sigma>1 + \<sigma>2')\<close>
          using IH2 st F by auto
        then show ?thesis
          using sep' by (simp add: sepalg_comm)
      qed (use F in auto)
    qed (auto elim: lift_right.elims)
    \<comment> \<open>The scheduling point itself.\<close>
    show ?case
    proof (rule safe.safeI)
      show \<open>is_local (atomic_step y (par e1 e2)) {\<sigma>1 + \<sigma>2}\<close>
        using is_local_par[OF y(1)] .
    next
      fix e' \<sigma>' assume \<open>atomic_step y (par e1 e2) (\<sigma>1 + \<sigma>2) (Continue e', \<sigma>')\<close>
      then show \<open>safe y (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) e' \<sigma>'\<close>
        using left right comm by (auto simp add: atomic_step_par[OF y(1)])
    qed (auto simp add: atomic_step_par[OF y(1)])
  qed
qed

text\<open>The disjoint parallel rule of concurrent separation logic.\<close>

theorem ctriple_par:
  assumes \<open>ctriple \<Gamma> P1 e1 Q1\<close>
      and \<open>ctriple \<Gamma> P2 e2 Q2\<close>
    shows \<open>ctriple \<Gamma> (P1 \<star> P2) (par e1 e2) (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2)\<close>
  using assms by (auto simp add: ctriple_def elim!: asepconjE intro!: safe_par)

text\<open>For comparison: the frame rule also holds for the concurrent triple.\<close>

theorem ctriple_frame:
  assumes \<open>ctriple \<Gamma> P e Q\<close>
    shows \<open>ctriple \<Gamma> (P \<star> R) e (\<lambda>v. Q v \<star> R)\<close>
proof -
  have \<open>safe (yh \<Gamma>) (\<lambda>v. Q v \<star> R) (bind e (\<lambda>v. literal v)) (s + r)\<close>
    if \<open>s \<Turnstile> P\<close> \<open>r \<Turnstile> R\<close> \<open>s \<sharp> r\<close> for s r
  proof -
    have saf: \<open>safe (yh \<Gamma>) Q e s\<close>
      using that assms by (simp add: ctriple_def)
    have post: \<open>s' + r \<Turnstile> Q v \<star> R\<close> if \<open>s' \<Turnstile> Q v\<close> \<open>s' \<sharp> r\<close> for s' v
      using that \<open>r \<Turnstile> R\<close> by (auto intro!: asepconjI)
    show ?thesis
      using safe_bind_literal[where Q'=\<open>\<lambda>v. Q v \<star> R\<close> and g=\<open>\<lambda>v. v\<close>, OF saf \<open>s \<sharp> r\<close> post]
      by simp
  qed
  then show ?thesis
    by (auto simp add: ctriple_def bind_literal_unit2 elim!: asepconjE)
qed

text\<open>Consequence (post-condition weakening and precondition strengthening).\<close>

lemma safe_post_weaken:
  assumes \<open>safe y Q e \<sigma>\<close>
      and \<open>\<And>v. Q v \<longlongrightarrow> Q' v\<close>
    shows \<open>safe y Q' e \<sigma>\<close>
  using assms(1)
proof (induction rule: safe.induct)
  case (safeI e \<sigma>)
  show ?case
  proof (rule safe.safeI)
    fix v \<sigma>' assume \<open>atomic_step y e \<sigma> (Finished v, \<sigma>')\<close>
    then show \<open>\<sigma>' \<Turnstile> Q' v\<close>
      using safeI.hyps(2) assms(2) by (meson aentailsE)
  qed (use safeI in blast)+
qed

lemma ctriple_consequence:
  assumes \<open>ctriple \<Gamma> P' e Q'\<close>
      and \<open>P \<longlongrightarrow> P'\<close>
      and \<open>\<And>v. Q' v \<longlongrightarrow> Q v\<close>
    shows \<open>ctriple \<Gamma> P e Q\<close>
  using assms by (auto simp add: ctriple_def intro: safe_post_weaken elim: aentailsE)

subsection\<open>Adequacy: from the concurrent triple to the existing sequential triple\<close>

text\<open>Finally, \<^verbatim>\<open>ctriple\<close> is connected to the existing semantics and logic: a safe expression,
deeply evaluated with the existing \<^term>\<open>deep_evaluates_nondet_basic\<close>, only produces successful
results, these satisfy the post-condition, and the whole evaluation is local in the sense of
\<^term>\<open>is_local\<close>.  So \<^verbatim>\<open>ctriple\<close> implies \<^verbatim>\<open>sstriple\<close> (with \<^term>\<open>\<bottom>\<close> for returns and aborts).
Applied to \<^verbatim>\<open>par\<close>, this means: \<^bold>\<open>every\<close> interleaving of the two threads (all answers to
every \<^term>\<open>NondetOrder\<close>) ends in \<^verbatim>\<open>Q1 v1 \<star> Q2 v2\<close>.  The proofs are rule inductions on
\<^verbatim>\<open>safe\<close>, following \<^term>\<open>deep_evaluates_nondet_basic_atomic_step\<close>.\<close>

lemma safe_deep_frame:
  assumes \<open>safe y Q e \<sigma>\<close>
      and \<open>\<sigma> \<sharp> \<rho>\<close>
      and \<open>c \<in> deep_evaluates_nondet_basic y e (\<sigma> + \<rho>)\<close>
    shows \<open>\<exists>v \<sigma>'. c = Success v (\<sigma>' + \<rho>) \<and> \<sigma>' \<sharp> \<rho> \<and> Success v \<sigma>' \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
  using assms
proof (induction arbitrary: c rule: safe.induct)
  case (safeI e \<sigma>)
  from safeI.prems(2) consider
      (fin) v \<tau> where \<open>atomic_step y e (\<sigma> + \<rho>) (Finished v, \<tau>)\<close> \<open>c = Success v \<tau>\<close>
    | (ret) r \<tau> where \<open>atomic_step y e (\<sigma> + \<rho>) (Returned r, \<tau>)\<close>
    | (abort) a \<tau> where \<open>atomic_step y e (\<sigma> + \<rho>) (Aborted a, \<tau>)\<close>
    | (cont) e' \<tau> where \<open>atomic_step y e (\<sigma> + \<rho>) (Continue e', \<tau>)\<close>
                         \<open>c \<in> deep_evaluates_nondet_basic y e' \<tau>\<close>
    by (subst (asm) deep_evaluates_nondet_basic_atomic_step) blast
  then show ?case
  proof cases
    case fin
    then show ?thesis
      using is_local_frame_step[OF safeI.hyps(1) safeI.prems(1)]
      by (metis deep_evaluates_nondet_basic_atomic_step)
  next
    case ret
    then show ?thesis
      using is_local_frame_step[OF safeI.hyps(1) safeI.prems(1)] safeI.hyps(3) by metis
  next
    case abort
    then show ?thesis
      using is_local_frame_step[OF safeI.hyps(1) safeI.prems(1)] safeI.hyps(4) by metis
  next
    case cont
    then obtain \<sigma>' where \<open>atomic_step y e \<sigma> (Continue e', \<sigma>')\<close> \<open>\<sigma>' \<sharp> \<rho>\<close> \<open>\<tau> = \<sigma>' + \<rho>\<close>
      using is_local_frame_step[OF safeI.hyps(1) safeI.prems(1)] by metis
    with cont safeI.IH show ?thesis
      by (metis deep_evaluates_nondet_basic_atomic_step)
  qed
qed

lemma safe_deep_frame_rev:
  assumes \<open>safe y Q e \<sigma>\<close>
      and \<open>\<sigma> \<sharp> \<rho>\<close>
      and \<open>Success v \<sigma>' \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
    shows \<open>\<sigma>' \<sharp> \<rho> \<and> Success v (\<sigma>' + \<rho>) \<in> deep_evaluates_nondet_basic y e (\<sigma> + \<rho>)\<close>
  using assms
proof (induction arbitrary: \<sigma>' rule: safe.induct)
  case (safeI e \<sigma>)
  note frame = is_local_singletonD[OF safeI.hyps(1) safeI.prems(1)]
  from safeI.prems(2) consider
      (fin) \<open>atomic_step y e \<sigma> (Finished v, \<sigma>')\<close>
    | (cont) e' \<tau> where \<open>atomic_step y e \<sigma> (Continue e', \<tau>)\<close>
                         \<open>Success v \<sigma>' \<in> deep_evaluates_nondet_basic y e' \<tau>\<close>
    by (subst (asm) deep_evaluates_nondet_basic_atomic_step) blast
  then show ?case
  proof cases
    case fin
    then show ?thesis
      using frame by (subst deep_evaluates_nondet_basic_atomic_step) blast
  next
    case cont
    then have \<open>\<tau> \<sharp> \<rho>\<close> \<open>atomic_step y e (\<sigma> + \<rho>) (Continue e', \<tau> + \<rho>)\<close>
      using frame by blast+
    with cont safeI.IH show ?thesis
      by (subst deep_evaluates_nondet_basic_atomic_step) blast
  qed
qed

lemma safe_deep_post:
  assumes \<open>safe y Q e \<sigma>\<close>
      and \<open>Success v \<sigma>' \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
    shows \<open>\<sigma>' \<Turnstile> Q v\<close>
  using assms
proof (induction arbitrary: \<sigma>' rule: safe.induct)
  case (safeI e \<sigma>)
  then show ?case
    by (subst (asm) deep_evaluates_nondet_basic_atomic_step) blast
qed

lemma safe_deep_success:
  assumes \<open>safe y Q e \<sigma>\<close>
      and \<open>c \<in> deep_evaluates_nondet_basic y e \<sigma>\<close>
    shows \<open>\<exists>v \<sigma>'. c = Success v \<sigma>'\<close>
proof -
  have \<open>c \<in> deep_evaluates_nondet_basic y e (\<sigma> + 0)\<close>
    using assms(2) by simp
  from safe_deep_frame[OF assms(1) zero_disjoint this] show ?thesis
    by auto
qed

theorem ctriple_sstriple:
  assumes \<open>ctriple \<Gamma> P e Q\<close>
    shows \<open>\<Gamma> ; P \<turnstile> e \<stileturn> Q \<bowtie> \<bottom> \<bowtie> \<bottom>\<close>
proof -
  have safe: \<open>safe (yh \<Gamma>) Q e \<sigma>\<close> if \<open>\<sigma> \<Turnstile> P\<close> for \<sigma>
    using assms that by (simp add: ctriple_def)
  \<comment> \<open>Locality of an evaluation relation that never fires from a safe state.\<close>
  have no_result_local: \<open>is_local R P\<close>
    if \<open>\<And>\<sigma> \<rho> t \<sigma>'. \<sigma> \<Turnstile> P \<Longrightarrow> \<sigma> \<sharp> \<rho> \<Longrightarrow> \<not> R (\<sigma> + \<rho>) (t, \<sigma>')\<close>
    for R :: \<open>'a \<Rightarrow> ('t \<times> 'a) \<Rightarrow> bool\<close>
  proof -
    have \<open>\<not> R \<sigma> (t, \<sigma>')\<close> if \<open>\<sigma> \<Turnstile> P\<close> for \<sigma> t \<sigma>'
      using that \<open>\<And>\<sigma> \<rho> t \<sigma>'. \<sigma> \<Turnstile> P \<Longrightarrow> \<sigma> \<sharp> \<rho> \<Longrightarrow> \<not> R (\<sigma> + \<rho>) (t, \<sigma>')\<close>[of \<sigma> 0] by simp
    with that show ?thesis
      by (auto simp add: is_local_def)
  qed
  show ?thesis
  proof (intro sstripleI)
    show \<open>P \<turnstile> eval_value (yh \<Gamma>) e \<stileturn>\<^sub>R Q\<close>
    proof (unfold atriple_rel_def, intro conjI allI impI is_localI)
      fix \<sigma> \<sigma>' v assume \<open>eval_value (yh \<Gamma>) e \<sigma> (v, \<sigma>')\<close> \<open>\<sigma> \<Turnstile> P\<close>
      then show \<open>\<sigma>' \<Turnstile> Q v\<close>
        using safe_deep_post[OF safe[OF \<open>\<sigma> \<Turnstile> P\<close>]]
        by (simp add: eval_value_def evaluates_to_value_def)
    next
      fix \<sigma> \<rho> \<sigma>' v
      assume \<open>\<sigma> \<sharp> \<rho>\<close> \<open>\<sigma> \<Turnstile> P\<close> \<open>eval_value (yh \<Gamma>) e \<sigma> (v, \<sigma>')\<close>
      then have \<open>Success v \<sigma>' \<in> deep_evaluates_nondet_basic (yh \<Gamma>) e \<sigma>\<close>
        by (simp add: eval_value_def evaluates_to_value_def)
      then show \<open>\<sigma>' \<sharp> \<rho>\<close>
        using safe_deep_frame_rev[OF safe[OF \<open>\<sigma> \<Turnstile> P\<close>] \<open>\<sigma> \<sharp> \<rho>\<close>] by blast
    next
      fix \<sigma> \<rho> \<tau> v
      assume \<open>\<sigma> \<sharp> \<rho>\<close> \<open>\<sigma> \<Turnstile> P\<close> \<open>eval_value (yh \<Gamma>) e (\<sigma> + \<rho>) (v, \<tau>)\<close>
      then show \<open>\<exists>\<sigma>'. eval_value (yh \<Gamma>) e \<sigma> (v, \<sigma>') \<and> \<tau> = \<sigma>' + \<rho>\<close>
        using safe_deep_frame[OF safe[OF \<open>\<sigma> \<Turnstile> P\<close>] \<open>\<sigma> \<sharp> \<rho>\<close>]
        by (fastforce simp add: eval_value_def evaluates_to_value_def)
    next
      fix \<sigma> \<rho> \<sigma>' \<tau> v
      assume \<open>\<sigma> \<sharp> \<rho>\<close> \<open>\<sigma> \<Turnstile> P\<close> \<open>eval_value (yh \<Gamma>) e \<sigma> (v, \<sigma>') \<and> \<tau> = \<sigma>' + \<rho>\<close>
      then show \<open>eval_value (yh \<Gamma>) e (\<sigma> + \<rho>) (v, \<tau>)\<close>
        using safe_deep_frame_rev[OF safe[OF \<open>\<sigma> \<Turnstile> P\<close>] \<open>\<sigma> \<sharp> \<rho>\<close>]
        by (simp add: eval_value_def evaluates_to_value_def)
    qed
  next
    have no_ret: \<open>\<not> eval_return (yh \<Gamma>) e (\<sigma> + \<rho>) (r, \<tau>)\<close> if \<open>\<sigma> \<Turnstile> P\<close> \<open>\<sigma> \<sharp> \<rho>\<close> for \<sigma> \<rho> r \<tau>
      using safe_deep_frame[OF safe[OF \<open>\<sigma> \<Turnstile> P\<close>] \<open>\<sigma> \<sharp> \<rho>\<close>]
      by (auto simp add: eval_return_def evaluates_to_return_def)
    show \<open>P \<turnstile> eval_return (yh \<Gamma>) e \<stileturn>\<^sub>R \<bottom>\<close>
      unfolding atriple_rel_def
    proof (intro conjI no_result_local allI impI)
      fix \<sigma> \<sigma>' r assume \<open>eval_return (yh \<Gamma>) e \<sigma> (r, \<sigma>')\<close> \<open>\<sigma> \<Turnstile> P\<close>
      then show \<open>\<sigma>' \<Turnstile> \<bottom> r\<close>
        using no_ret[of \<sigma> 0] by simp
    qed (use no_ret in blast)
  next
    have no_abort: \<open>\<not> eval_abort (yh \<Gamma>) e (\<sigma> + \<rho>) (a, \<tau>)\<close> if \<open>\<sigma> \<Turnstile> P\<close> \<open>\<sigma> \<sharp> \<rho>\<close> for \<sigma> \<rho> a \<tau>
      using safe_deep_frame[OF safe[OF \<open>\<sigma> \<Turnstile> P\<close>] \<open>\<sigma> \<sharp> \<rho>\<close>]
      by (auto simp add: eval_abort_def evaluates_to_abort_def)
    show \<open>P \<turnstile> eval_abort (yh \<Gamma>) e \<stileturn>\<^sub>R \<bottom>\<close>
      unfolding atriple_rel_def
    proof (intro conjI no_result_local allI impI)
      fix \<sigma> \<sigma>' a assume \<open>eval_abort (yh \<Gamma>) e \<sigma> (a, \<sigma>')\<close> \<open>\<sigma> \<Turnstile> P\<close>
      then show \<open>\<sigma>' \<Turnstile> \<bottom> a\<close>
        using no_abort[of \<sigma> 0] by simp
    qed (use no_abort in blast)
  qed
qed

text\<open>Putting the pieces together: the disjoint parallel rule, stated with the \<^emph>\<open>existing\<close>
sequential triple for the composite program.\<close>

corollary sstriple_par:
  assumes \<open>ctriple \<Gamma> P1 e1 Q1\<close>
      and \<open>ctriple \<Gamma> P2 e2 Q2\<close>
    shows \<open>\<Gamma> ; P1 \<star> P2 \<turnstile> par e1 e2 \<stileturn> (\<lambda>(v1, v2). Q1 v1 \<star> Q2 v2) \<bowtie> \<bottom> \<bowtie> \<bottom>\<close>
  using ctriple_sstriple[OF ctriple_par[OF assms]] .

declare sepalg_comm[simp]

(*<*)
end
(*>*)

end
