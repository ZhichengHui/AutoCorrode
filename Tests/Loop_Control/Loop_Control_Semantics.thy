(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Loop_Control_Semantics
  imports Shallow_Micro_Rust.Shallow_Micro_Rust
begin
(*>*)

section\<open>Semantics of \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close>\<close>

text\<open>The tests run small closed uRust programs on a state that is a trace of natural numbers:
\<^term>\<open>tick n\<close> appends \<^term>\<open>n\<close> to the trace, and \<^term>\<open>len_eq k\<close>, \<^term>\<open>len_lt k\<close> and
\<^term>\<open>next_below k\<close> inspect its length. Each test states the outcome and the final trace of the
program; the comment above it gives the Rust program with the same behaviour, where
\<^verbatim>\<open>t\<close> is the trace (a \<^verbatim>\<open>Vec\<close>).\<close>

definition tick :: \<open>nat \<Rightarrow> (nat list, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>tick n \<equiv> Expression (\<lambda>\<sigma>. Success () (\<sigma> @ [n]))\<close>

definition len_eq :: \<open>nat \<Rightarrow> (nat list, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>len_eq k \<equiv> Expression (\<lambda>\<sigma>. Success (length \<sigma> = k) \<sigma>)\<close>

definition len_lt :: \<open>nat \<Rightarrow> (nat list, bool, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>len_lt k \<equiv> Expression (\<lambda>\<sigma>. Success (length \<sigma> < k) \<sigma>)\<close>

definition next_below :: \<open>nat \<Rightarrow> (nat list, nat option, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>next_below k \<equiv> Expression (\<lambda>\<sigma>. Success (if length \<sigma> < k then Some (length \<sigma>) else None) \<sigma>)\<close>

definition len_pair :: \<open>nat \<Rightarrow> (nat list, nat \<times> bool \<times> tnil, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>len_pair k \<equiv> Expression (\<lambda>\<sigma>. Success (length \<sigma>, length \<sigma> < k, TNil) \<sigma>)\<close>

datatype ('v, 'r) outcome = OSuccess 'v \<open>nat list\<close> | OReturn 'r \<open>nat list\<close>
  | OAbort \<open>unit abort\<close> \<open>nat list\<close> | OYield

fun outcome_of :: \<open>(nat list, 'v, 'r, unit, 'i, 'o) continuation \<Rightarrow> ('v, 'r) outcome\<close> where
  \<open>outcome_of (Success v \<sigma>) = OSuccess v \<sigma>\<close>
| \<open>outcome_of (Return r \<sigma>) = OReturn r \<sigma>\<close>
| \<open>outcome_of (Abort a \<sigma>) = OAbort a \<sigma>\<close>
| \<open>outcome_of (Yield _ _ _) = OYield\<close>

type_synonym ('v, 'r) prog = \<open>(nat list, 'v, 'r, unit, unit prompt, unit prompt_output) expression\<close>

definition run :: \<open>('v, 'r) prog \<Rightarrow> ('v, 'r) outcome\<close> where
  \<open>run e \<equiv> outcome_of (evaluate e [])\<close>

lemma evaluate_Expression:
  shows \<open>evaluate (Expression f) \<sigma> = f \<sigma>\<close>
  by (simp add: evaluate_def)

lemma bounded_while_numeral:
  shows \<open>bounded_while lbl (numeral k) cond body =
     bind (loop_step lbl (bind cond (\<lambda>c. if c then sequence body (literal True) else literal False)))
       (\<lambda>c. if c then bounded_while lbl (pred_numeral k) cond body else skip)\<close>
  by (simp add: numeral_eq_Suc)

lemmas run_simps = bounded_while_numeral two_armed_conditional_def propagate_option_def run_def tick_def len_eq_def len_lt_def next_below_def len_pair_def
  list_into_iter_def micro_rust_simps for_loop_list evaluate_loop_step bind_evaluate sequence_def
  evaluate_Expression

subsection\<open>\<^verbatim>\<open>for\<close>\<close>

text\<open>\<^verbatim>\<open>for i in [1,2,3,4] { t.push(i); if i == 2 { break; } t.push(10*i); } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2, 3, 4]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      if \<llangle>i = 2\<rrangle> { break; }
      \<epsilon>\<open>tick (10 * i)\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 10, 2, 99]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>for i in [1,2,3] { t.push(i); if i == 2 { continue; } t.push(10*i); } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2, 3]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      if \<llangle>i = 2\<rrangle> { continue; }
      \<epsilon>\<open>tick (10 * i)\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 10, 2, 3, 30, 99]\<close>
  by (simp add: run_simps)

text\<open>A \<^verbatim>\<open>continue\<close> in the last iteration and a \<^verbatim>\<open>break\<close> in the first one:\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      continue;
    }
    for i in (\<llangle>[3::nat, 4]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      break;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 2, 3, 99]\<close>
  by (simp add: run_simps)

subsection\<open>\<^verbatim>\<open>while\<close>\<close>

text\<open>\<^verbatim>\<open>while t.len() < 5 { t.push(1); if t.len() == 3 { break; } t.push(2); } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] while (\<epsilon>\<open>len_lt 5\<close>) {
      \<epsilon>\<open>tick 1\<close>;
      if \<epsilon>\<open>len_eq 3\<close> { break; }
      \<epsilon>\<open>tick 2\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 2, 1, 99]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>while t.len() < 5 { t.push(1); if t.len() == 3 { continue; } t.push(2); } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] while (\<epsilon>\<open>len_lt 5\<close>) {
      \<epsilon>\<open>tick 1\<close>;
      if \<epsilon>\<open>len_eq 3\<close> { continue; }
      \<epsilon>\<open>tick 2\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 2, 1, 1, 2, 99]\<close>
  by (simp add: run_simps)

subsection\<open>\<^verbatim>\<open>loop\<close>\<close>

text\<open>\<^verbatim>\<open>loop { t.push(1); if t.len() == 3 { break; } } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] loop {
      \<epsilon>\<open>tick 1\<close>;
      if \<epsilon>\<open>len_eq 3\<close> { break; }
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 1, 1, 99]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>loop { t.push(1); if t.len() == 1 { continue; } t.push(2); if t.len() < 5 { continue; } break; }
t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] loop {
      \<epsilon>\<open>tick 1\<close>;
      if \<epsilon>\<open>len_eq 1\<close> { continue; }
      \<epsilon>\<open>tick 2\<close>;
      if \<epsilon>\<open>len_lt 5\<close> { continue; }
      break;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 1, 2, 1, 2, 99]\<close>
  by (simp add: run_simps)

subsection\<open>\<^verbatim>\<open>while let\<close>\<close>

text\<open>\<^verbatim>\<open>while let Some(x) = next_below(6) { t.push(x); if x == 2 { continue; } t.push(10);
if x >= 3 { break; } } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] while let Some(x) = \<epsilon>\<open>next_below 6\<close> {
      \<epsilon>\<open>tick x\<close>;
      if \<llangle>x = 2\<rrangle> { continue; }
      \<epsilon>\<open>tick 10\<close>;
      if \<llangle>3 \<le> x\<rrangle> { break; }
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [0, 10, 2, 3, 10, 99]\<close>
  by (simp add: run_simps)

text\<open>Tuple pattern: \<^verbatim>\<open>while let (a, b) = (t.len(), t.len() < 4) { t.push(a); if a == 2 { continue; }
t.push(10); if !b { break; } } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] while let (a, b) = \<epsilon>\<open>len_pair 4\<close> {
      \<epsilon>\<open>tick a\<close>;
      if \<llangle>a = 2\<rrangle> { continue; }
      \<epsilon>\<open>tick 10\<close>;
      if \<llangle>\<not> b\<rrangle> { break; }
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [0, 10, 2, 3, 10, 5, 10, 99]\<close>
  by (simp add: run_simps)

subsection\<open>Labeled \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> in the condition of a loop\<close>

text\<open>\<^verbatim>\<open>'w: while { t.push(1); if t.len() == 3 { break 'w; } true } { t.push(2); } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] 'w: while ({ \<epsilon>\<open>tick 1\<close>; if \<epsilon>\<open>len_eq 3\<close> { break 'w; } \<llangle>True\<rrangle> }) {
      \<epsilon>\<open>tick 2\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 2, 1, 99]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>'w: while { t.push(1); if t.len() == 1 { continue 'w; } t.len() < 4 } { t.push(2); }
t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] 'w: while ({ \<epsilon>\<open>tick 1\<close>; if \<epsilon>\<open>len_eq 1\<close> { continue 'w; } \<epsilon>\<open>len_lt 4\<close> }) {
      \<epsilon>\<open>tick 2\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 1, 2, 1, 99]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>'w: while let Some(x) = { if t.len() == 2 { break 'w; } next_below(9) } { t.push(x); }
t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] 'w: while let Some(x) = ({ if \<epsilon>\<open>len_eq 2\<close> { break 'w; } \<epsilon>\<open>next_below 9\<close> }) {
      \<epsilon>\<open>tick x\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [0, 1, 99]\<close>
  by (simp add: run_simps)

text\<open>A labeled \<^verbatim>\<open>break\<close> in the condition of an inner \<^verbatim>\<open>while\<close> that names the outer loop:
\<^verbatim>\<open>'o: for i in [1,2] { t.push(i); while { if i == 2 { break 'o; } t.len() < 3 } { t.push(5); } }
t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    'o: for i in (\<llangle>[1::nat, 2]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      #[fuel(\<epsilon>\<open>10\<close>)] while ({ if \<llangle>i = 2\<rrangle> { break 'o; } \<epsilon>\<open>len_lt 3\<close> }) {
        \<epsilon>\<open>tick 5\<close>;
      }
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 5, 5, 2, 99]\<close>
  by (simp add: run_simps)

subsection\<open>Labeled \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> out of nested loops\<close>

text\<open>Outer \<^verbatim>\<open>for\<close>, inner \<^verbatim>\<open>while\<close>:
\<^verbatim>\<open>'o: for i in [1,2,3] { t.push(i); while true { t.push(10); if i == 2 { break 'o; } break; } }
t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    'o: for i in (\<llangle>[1::nat, 2, 3]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      #[fuel(\<epsilon>\<open>5\<close>)] while (\<llangle>True\<rrangle>) {
        \<epsilon>\<open>tick 10\<close>;
        if \<llangle>i = 2\<rrangle> { break 'o; }
        break;
      }
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 10, 2, 10, 99]\<close>
  by (simp add: run_simps)

text\<open>Outer \<^verbatim>\<open>loop\<close>, inner \<^verbatim>\<open>for\<close>:
\<^verbatim>\<open>'o: loop { if t.len() == 6 { break; } t.push(0); for j in [1,2,3] { t.push(j); if j == 2 { continue 'o; } }
t.push(9); } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] 'o: loop {
      if \<epsilon>\<open>len_eq 6\<close> { break; }
      \<epsilon>\<open>tick 0\<close>;
      for j in (\<llangle>[1::nat, 2, 3]\<rrangle>) {
        \<epsilon>\<open>tick j\<close>;
        if \<llangle>j = 2\<rrangle> { continue 'o; }
      }
      \<epsilon>\<open>tick 9\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [0, 1, 2, 0, 1, 2, 99]\<close>
  by (simp add: run_simps)

text\<open>Outer \<^verbatim>\<open>while let\<close>, inner \<^verbatim>\<open>loop\<close>:
\<^verbatim>\<open>'o: while let Some(x) = next_below(10) { t.push(x); loop { t.push(7); if t.len() == 4 { break 'o; }
break; } } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] 'o: while let Some(x) = \<epsilon>\<open>next_below 10\<close> {
      \<epsilon>\<open>tick x\<close>;
      #[fuel(\<epsilon>\<open>10\<close>)] loop {
        \<epsilon>\<open>tick 7\<close>;
        if \<epsilon>\<open>len_eq 4\<close> { break 'o; }
        break;
      }
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [0, 7, 2, 7, 99]\<close>
  by (simp add: run_simps)

text\<open>Outer \<^verbatim>\<open>while\<close>: a labeled \<^verbatim>\<open>continue\<close> evaluates the condition of the outer loop again:
\<^verbatim>\<open>'o: while t.len() < 4 { t.push(1); for j in [1,2] { t.push(2); continue 'o; } t.push(3); }
t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] 'o: while (\<epsilon>\<open>len_lt 4\<close>) {
      \<epsilon>\<open>tick 1\<close>;
      for j in (\<llangle>[1::nat, 2]\<rrangle>) {
        \<epsilon>\<open>tick 2\<close>;
        continue 'o;
      }
      \<epsilon>\<open>tick 3\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 2, 1, 2, 99]\<close>
  by (simp add: run_simps)

text\<open>Three loops; the innermost, unlabeled loop passes on \<^verbatim>\<open>break 'b\<close> and \<^verbatim>\<open>break 'a\<close>:
\<^verbatim>\<open>'a: for i in [1,2,3] { 'b: loop { for j in [1,2] { t.push(10*i+j); if i == 1 { break 'b; }
if i == 2 && j == 2 { break 'a; } } break; } t.push(0); } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    'a: for i in (\<llangle>[1::nat, 2, 3]\<rrangle>) {
      #[fuel(\<epsilon>\<open>10\<close>)] 'b: loop {
        for j in (\<llangle>[1::nat, 2]\<rrangle>) {
          \<epsilon>\<open>tick (10 * i + j)\<close>;
          if \<llangle>i = 1\<rrangle> { break 'b; }
          if \<llangle>i = 2 \<and> j = 2\<rrangle> { break 'a; }
        }
        break;
      }
      \<epsilon>\<open>tick 0\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [11, 0, 21, 22, 99]\<close>
  by (simp add: run_simps)

subsection\<open>Shadowed labels\<close>

text\<open>The innermost loop with a label catches a \<^verbatim>\<open>break\<close> or \<^verbatim>\<open>continue\<close> naming it (Rust warns
about the shadowed label but accepts the program):
\<^verbatim>\<open>'a: for i in [1,2] { t.push(i); 'a: loop { t.push(5); break 'a; } t.push(6); } t.push(99);\<close>\<close>
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
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 5, 6, 2, 5, 6, 99]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>'a: for i in [1,2] { t.push(i); 'a: while t.len() < 3 { t.push(5); continue 'a; } t.push(6); }
t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    'a: for i in (\<llangle>[1::nat, 2]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      #[fuel(\<epsilon>\<open>10\<close>)] 'a: while (\<epsilon>\<open>len_lt 3\<close>) {
        \<epsilon>\<open>tick 5\<close>;
        continue 'a;
      }
      \<epsilon>\<open>tick 6\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 5, 5, 6, 2, 6, 99]\<close>
  by (simp add: run_simps)

subsection\<open>\<^verbatim>\<open>return\<close> and \<^verbatim>\<open>?\<close> leave the function, not the loop\<close>

text\<open>\<^verbatim>\<open>for i in [1,2,3] { t.push(i); if i == 2 { return 42; } } t.push(99); 0\<close>\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2, 3]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      if \<llangle>i = 2\<rrangle> { return \<llangle>42 :: nat\<rrangle>; }
    }
    \<epsilon>\<open>tick 99\<close>;
    \<llangle>0 :: nat\<rrangle>
  \<rbrakk> :: (nat, nat) prog) = OReturn 42 [1, 2]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>loop { for i in [1,2] { t.push(i); if i == 2 { return 7; } } t.push(0); } t.push(99); 0\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] loop {
      for i in (\<llangle>[1::nat, 2]\<rrangle>) {
        \<epsilon>\<open>tick i\<close>;
        if \<llangle>i = 2\<rrangle> { return \<llangle>7 :: nat\<rrangle>; }
      }
      \<epsilon>\<open>tick 0\<close>;
    }
    \<epsilon>\<open>tick 99\<close>;
    \<llangle>0 :: nat\<rrangle>
  \<rbrakk> :: (nat, nat) prog) = OReturn 7 [1, 2]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>while { t.push(1); if t.len() == 3 { return 5; } true } { t.push(2); } t.push(99); 0\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] while ({ \<epsilon>\<open>tick 1\<close>; if \<epsilon>\<open>len_eq 3\<close> { return \<llangle>5 :: nat\<rrangle>; } \<llangle>True\<rrangle> }) {
      \<epsilon>\<open>tick 2\<close>;
    }
    \<epsilon>\<open>tick 99\<close>;
    \<llangle>0 :: nat\<rrangle>
  \<rbrakk> :: (nat, nat) prog) = OReturn 5 [1, 2, 1]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>for i in [1,2,3] { t.push(i); (if i == 2 { None } else { Some(()) })?; t.push(10); }
t.push(99); Some(0)\<close>\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2, 3]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      \<llangle>if i = 2 then None else Some ()\<rrangle>?;
      \<epsilon>\<open>tick 10\<close>;
    }
    \<epsilon>\<open>tick 99\<close>;
    \<llangle>Some (0 :: nat)\<rrangle>
  \<rbrakk> :: (nat option, nat option) prog) = OReturn None [1, 10, 2]\<close>
  by (simp add: run_simps)

subsection\<open>\<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> inside other constructs\<close>

text\<open>\<^verbatim>\<open>for i in [1,2,3,4] { match f(i) { Some(x) => { if x == 3 { break; } t.push(x); }, None => { continue; } };
t.push(10); } t.push(99);\<close> where \<^verbatim>\<open>f(2) = None\<close> and \<^verbatim>\<open>f(i) = Some(i)\<close> otherwise.\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2, 3, 4]\<rrangle>) {
      match \<llangle>if i = 2 then None else Some i\<rrangle> {
        Some(x) \<Rightarrow> { if \<llangle>x = 3\<rrangle> { break; } \<epsilon>\<open>tick x\<close>; },
        None \<Rightarrow> { continue; }
      };
      \<epsilon>\<open>tick 10\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 10, 99]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>for i in [1,2,3,4] { if let Some(x) = f(i) { t.push(x); } else { continue; } if i == 3 { break; }
t.push(10); } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2, 3, 4]\<rrangle>) {
      if let Some(x) = \<llangle>if i = 2 then None else Some i\<rrangle> { \<epsilon>\<open>tick x\<close>; } else { continue; }
      if \<llangle>i = 3\<rrangle> { break; }
      \<epsilon>\<open>tick 10\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 10, 3, 99]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>for i in [1,2,3,4] { let Some(x) = f(i) else { continue; }; t.push(x); if x == 3 { break; } }
t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2, 3, 4]\<rrangle>) {
      let Some(x) = \<llangle>if i = 2 then None else Some i\<rrangle> else { continue; };
      \<epsilon>\<open>tick x\<close>;
      if \<llangle>x = 3\<rrangle> { break; }
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 3, 99]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>for i in [1,2,3] { { t.push(i); unsafe { if i == 2 { break; } } } t.push(10); } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2, 3]\<rrangle>) {
      { \<epsilon>\<open>tick i\<close>; unsafe { if \<llangle>i = 2\<rrangle> { break; } } }
      \<epsilon>\<open>tick 10\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 10, 2, 99]\<close>
  by (simp add: run_simps)

text\<open>\<^verbatim>\<open>break\<close> as the value of an \<^verbatim>\<open>if\<close>:
\<^verbatim>\<open>for i in [1,2,3] { let y = if i == 2 { break; } else { 10*i }; t.push(y); } t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2, 3]\<rrangle>) {
      let y = if \<llangle>i = 2\<rrangle> { break; } else { \<llangle>10 * i\<rrangle> };
      \<epsilon>\<open>tick y\<close>;
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [10, 99]\<close>
  by (simp add: run_simps)

text\<open>An unlabeled \<^verbatim>\<open>break\<close> in the iterator expression of a \<^verbatim>\<open>for\<close> loop belongs to the
enclosing loop: \<^verbatim>\<open>loop { t.push(1); for i in (if t.len() == 3 { break; } else { vec![3] }) { t.push(i); } }
t.push(99);\<close>\<close>
lemma \<open>run (\<lbrakk>
    #[fuel(\<epsilon>\<open>10\<close>)] loop {
      \<epsilon>\<open>tick 1\<close>;
      for i in (if \<epsilon>\<open>len_eq 3\<close> { break; } else { \<llangle>[3::nat]\<rrangle> }) {
        \<epsilon>\<open>tick i\<close>;
      }
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OSuccess () [1, 3, 1, 99]\<close>
  by eval

text\<open>Other aborts pass through loops:\<close>
lemma \<open>run (\<lbrakk>
    for i in (\<llangle>[1::nat, 2]\<rrangle>) {
      \<epsilon>\<open>tick i\<close>;
      panic!("x");
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) = OAbort (Panic (String.implode ''x'')) [1]\<close>
  by (simp add: run_simps)

subsection\<open>Fuel\<close>

text\<open>The old definition of \<^term>\<open>bounded_while\<close>, before loop control:\<close>
fun old_bounded_while :: \<open>nat \<Rightarrow> ('s, bool, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, unit, 'r, 'abort, 'i, 'o) expression \<Rightarrow> ('s, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>old_bounded_while 0 cond body = skip\<close>
| \<open>old_bounded_while (Suc n) cond body =
     bind cond (\<lambda>c. if c then sequence body (old_bounded_while n cond body) else skip)\<close>

text\<open>Every iteration uses one unit of fuel, also one that ends with \<^verbatim>\<open>continue\<close>. A loop that
runs out of fuel ends like a loop whose condition is false.\<close>
lemma \<open>run (\<lbrakk> #[fuel(\<epsilon>\<open>3\<close>)] loop { \<epsilon>\<open>tick 1\<close>; } \<epsilon>\<open>tick 99\<close> \<rbrakk> :: (unit, unit) prog)
         = OSuccess () [1, 1, 1, 99]\<close>
  by (simp add: run_simps)

lemma \<open>run (\<lbrakk> #[fuel(\<epsilon>\<open>3\<close>)] loop { \<epsilon>\<open>tick 1\<close>; continue; } \<epsilon>\<open>tick 99\<close> \<rbrakk> :: (unit, unit) prog)
         = OSuccess () [1, 1, 1, 99]\<close>
  by (simp add: run_simps)

lemma \<open>run (\<lbrakk> #[fuel(\<epsilon>\<open>0\<close>)] while (\<llangle>True\<rrangle>) { \<epsilon>\<open>tick 1\<close>; } \<epsilon>\<open>tick 99\<close> \<rbrakk> :: (unit, unit) prog)
         = OSuccess () [99]\<close>
  by (simp add: run_simps)

lemma \<open>run (\<lbrakk> #[fuel(\<epsilon>\<open>2\<close>)] while (\<epsilon>\<open>len_lt 5\<close>) { \<epsilon>\<open>tick 1\<close>; } \<epsilon>\<open>tick 99\<close> \<rbrakk> :: (unit, unit) prog)
         = OSuccess () [1, 1, 99]\<close>
  by (simp add: run_simps)

text\<open>Without \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close>, loops behave as with the old definition, also when the
body returns or panics:\<close>
lemma \<open>run (bounded_while None n (len_lt 4) (tick 1) :: (unit, unit) prog)
         = run (old_bounded_while n (len_lt 4) (tick 1))\<close> if \<open>n \<in> {0, 1, 3, 4, 7}\<close>
  using that by (auto simp add: run_simps numeral_eq_Suc)

lemma \<open>run (bounded_while None n (len_lt 9) (sequence (tick 1) (two_armed_conditional (len_eq 3)
            (return_func (literal 5)) skip)) :: (unit, nat) prog)
         = run (old_bounded_while n (len_lt 9) (sequence (tick 1) (two_armed_conditional (len_eq 3)
            (return_func (literal 5)) skip)))\<close> if \<open>n \<in> {0, 2, 3, 4, 7}\<close>
  using that by (auto simp add: run_simps numeral_eq_Suc)

lemma \<open>run (bounded_while (Some STR ''a'') n (len_lt 9) (sequence (tick 1) (two_armed_conditional (len_eq 3)
            (panic STR ''p'') skip)) :: (unit, nat) prog)
         = run (old_bounded_while n (len_lt 9) (sequence (tick 1) (two_armed_conditional (len_eq 3)
            (panic STR ''p'') skip)))\<close> if \<open>n \<in> {0, 2, 3, 4, 7}\<close>
  using that by (auto simp add: run_simps numeral_eq_Suc)

subsection\<open>Yields inside loops\<close>

text\<open>A \<^verbatim>\<open>break\<close> after a yield is still caught by the loop:\<close>
lemma \<open>outcome_of (deep_evaluate_det yield_handler_det_no_yield (\<lbrakk>
    #[fuel(\<epsilon>\<open>5\<close>)] loop {
      \<y>\<i>\<e>\<l>\<d>;
      \<epsilon>\<open>tick 1\<close>;
      if \<epsilon>\<open>len_eq 2\<close> { break; }
    }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) []) = OSuccess () [1, 1, 99]\<close>
  by eval

lemma \<open>run (\<lbrakk> #[fuel(\<epsilon>\<open>5\<close>)] loop { \<y>\<i>\<e>\<l>\<d>; break; } \<rbrakk> :: (unit, unit) prog) = OYield\<close>
  by (simp add: run_simps pause_def)

lemma
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>yield_handler_no_yield, loop_step lbl (sequence pause (loop_break None))\<rangle> (False, \<sigma>)\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>v\<langle>yield_handler_no_yield, loop_step lbl (sequence pause (loop_continue None))\<rangle> (True, \<sigma>)\<close>
    and \<open>\<not> (\<sigma> \<leadsto>\<^sub>a\<langle>yield_handler_no_yield, loop_step lbl (sequence pause (loop_break None))\<rangle> (a, \<sigma>'))\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>yield_handler_no_yield, loop_step None (sequence pause (loop_break (Some STR ''a'')))\<rangle>
           (LoopBreak (Some STR ''a''), \<sigma>)\<close>
  by (auto simp add: urust_eval_predicate_loop_step urust_eval_predicate_simps loop_passes_def loop_abort_def)

text\<open>By design, an abort raised by the yield handler is not caught by a loop, even if it is
\<^term>\<open>LoopBreak None\<close>. Valid triple contexts exclude such yield handlers.\<close>
lemma \<open>outcome_of (deep_evaluate_det (\<lambda>_ _ \<sigma>. Abort (LoopBreak None) \<sigma>) (\<lbrakk>
    #[fuel(\<epsilon>\<open>5\<close>)] loop { \<y>\<i>\<e>\<l>\<d>; \<epsilon>\<open>tick 1\<close>; }
    \<epsilon>\<open>tick 99\<close>
  \<rbrakk> :: (unit, unit) prog) []) = OAbort (LoopBreak None) []\<close>
  by eval

subsection\<open>Loop combinators\<close>

lemma \<open>evaluate (bounded_while lbl (Suc n) (literal True) (loop_break None)) \<sigma> = Success () \<sigma>\<close>
  by (simp add: evaluate_loop_step bind_evaluate micro_rust_simps)

lemma \<open>evaluate (bounded_while (Some STR ''a'') (Suc n) (literal True) (loop_break (Some STR ''b''))) \<sigma>
         = Abort (LoopBreak (Some STR ''b'')) \<sigma>\<close>
  by (simp add: evaluate_loop_step bind_evaluate micro_rust_simps)

lemma \<open>evaluate (raw_for_loop lbl xs (\<lambda>_. loop_continue None)) \<sigma> = Success () \<sigma>\<close>
  by (induction xs) (simp_all add: raw_for_loop_cons evaluate_loop_step bind_evaluate micro_rust_simps)

lemma \<open>evaluate (raw_for_loop None xs (\<lambda>_. loop_continue (Some l))) \<sigma>
         = (if xs = [] then Success () \<sigma> else Abort (LoopContinue (Some l)) \<sigma>)\<close>
  by (cases xs) (simp_all add: raw_for_loop_cons evaluate_loop_step bind_evaluate micro_rust_simps)

(*<*)
end
(*>*)
