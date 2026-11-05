(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Loop_Control_Syntax
  imports
    Shallow_Micro_Rust.Micro_Rust_Shallow_Embedding
begin

section\<open>Parsing tests for \<^verbatim>\<open>break\<close>, \<^verbatim>\<open>continue\<close> and labeled loops\<close>

subsection\<open>Break and Continue\<close>

text\<open>\<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> become the aborts \<^term>\<open>LoopBreak l\<close> and
\<^term>\<open>LoopContinue l\<close>, which the loop catches. \<^verbatim>\<open>return\<close> and \<^verbatim>\<open>?\<close> are unchanged
inside loops.\<close>

context
  fixes n :: nat
begin
term \<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  #[fuel(\<epsilon>\<open>n\<close>)] loop {
    if *x == 10_u32 {
      break;
    }
    x += 1_u32;
  };
  *x
\<rbrakk>\<close>

term \<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  for i in (\<llangle>[1 :: 32 word, 2, 3]\<rrangle>) {
    if i == 2_u32 {
      continue;
    }
    x += i;
  };
  *x
\<rbrakk>\<close>
end

context
  fixes n m :: nat
    and v :: \<open>32 word\<close>
    and c :: bool
    and x :: \<open>32 word option\<close>
begin

lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { break; } \<rbrakk>
         = bounded_while None n (literal True) (loop_break None)\<close>
  by (rule refl)

lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while (\<llangle>c\<rrangle>) { continue; } \<rbrakk>
         = bounded_while None n (literal c) (loop_continue None)\<close>
  by (rule refl)

lemma \<open>(\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { return \<llangle>v\<rrangle>; } \<rbrakk>
          :: ('s, unit, 32 word, 'abort, 'i, 'o) expression)
         = bounded_while None n (literal True) (return_func (literal v))\<close>
  by (rule refl)

lemma \<open>(\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { \<llangle>x\<rrangle>?; () } \<rbrakk> :: ('s, unit, 32 word option, 'abort, 'i, 'o) expression)
         = bounded_while None n (literal True) (sequence (propagate_option (literal x)) (literal ()))\<close>
  by (rule refl)

\<comment>\<open>Nested loops: an unlabeled \<^verbatim>\<open>break\<close> names no loop; the inner loop catches it\<close>
lemma \<open>(\<lbrakk>
    #[fuel(\<epsilon>\<open>n\<close>)] loop {
      #[fuel(\<epsilon>\<open>m\<close>)] loop {
        if \<llangle>c\<rrangle> { break; } else { return \<llangle>v\<rrangle>; }
      }
    }
  \<rbrakk> :: ('s, unit, 32 word, 'abort, 'i, 'o) expression)
    = bounded_while None n (literal True) (bounded_while None m (literal True)
        (two_armed_conditional (literal c) (loop_break None) (return_func (literal v))))\<close>
  by (rule refl)

end

subsection\<open>Labeled Loops\<close>

context
  fixes n m :: nat
    and c :: bool
    and x :: \<open>32 word option\<close>
begin

term \<open>\<lbrakk>
  let mut s = \<llangle>0 :: 32 word\<rrangle>;
  'outer: for i in (\<llangle>[1 :: 32 word, 2, 3]\<rrangle>) {
    for j in (\<llangle>[1 :: 32 word, 2, 3]\<rrangle>) {
      if j == i {
        continue 'outer;
      }
      s += j;
    }
  };
  *s
\<rbrakk>\<close>

term \<open>\<lbrakk>
  #[fuel(\<epsilon>\<open>n\<close>)] 'a: while let Some(u) = \<llangle>x\<rrangle> {
    #[fuel(\<epsilon>\<open>m\<close>)] 'b: while (\<llangle>c\<rrangle>) {
      break 'a;
    }
  }
\<rbrakk>\<close>

lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'outer: loop { #[fuel(\<epsilon>\<open>m\<close>)] loop { break 'outer; } } \<rbrakk>
         = bounded_while (Some STR ''outer'') n (literal True) (bounded_while None m (literal True)
             (loop_break (Some STR ''outer'')))\<close>
  by (rule refl)

lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'outer: while (\<llangle>c\<rrangle>) { #[fuel(\<epsilon>\<open>m\<close>)] loop { continue 'outer; } } \<rbrakk>
         = bounded_while (Some STR ''outer'') n (literal c) (bounded_while None m (literal True)
             (loop_continue (Some STR ''outer'')))\<close>
  by (rule refl)

\<comment>\<open>A labeled \<^verbatim>\<open>break\<close> in the condition of a \<^verbatim>\<open>while\<close> loop may name that loop\<close>
lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: while ({ break 'a; }) { () } \<rbrakk>
         = bounded_while (Some STR ''a'') n (loop_break (Some STR ''a'')) (literal ())\<close>
  by (rule refl)

end

subsection\<open>Rejected Loop Control\<close>

text\<open>\<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> outside of a loop, including inside a closure within a
loop, with an unknown label, and without a label in the condition of a \<^verbatim>\<open>while\<close> loop are
rejected.\<close>

ML_val\<open>
  fun rejected s = not (can (Syntax.read_term \<^context>) s)
  val _ = \<^assert> (rejected "\<lbrakk> break; \<rbrakk>")
  val _ = \<^assert> (rejected "\<lbrakk> continue; \<rbrakk>")
  val _ = \<^assert> (rejected "\<lbrakk> break 'a; \<rbrakk>")
  val _ = \<^assert> (rejected "\<lbrakk> #[fuel(\<epsilon>\<open>0\<close>)] 'a: loop { break 'b; } \<rbrakk>")
  val _ = \<^assert> (rejected "\<lbrakk> #[fuel(\<epsilon>\<open>0\<close>)] loop { let f = ( |y| { break; } ); break; } \<rbrakk>")
  val _ = \<^assert> (rejected "\<lbrakk> #[fuel(\<epsilon>\<open>0\<close>)] 'a: loop { let f = ( |y| { break 'a; } ); break; } \<rbrakk>")
  val _ = \<^assert> (rejected "\<lbrakk> #[fuel(\<epsilon>\<open>0\<close>)] while ({ break; }) { () } \<rbrakk>")
  val _ = \<^assert> (rejected "\<lbrakk> #[fuel(\<epsilon>\<open>0\<close>)] 'a: while ({ continue; }) { () } \<rbrakk>")
  val _ = \<^assert> (not (rejected "\<lbrakk> #[fuel(\<epsilon>\<open>0\<close>)] 'a: while ({ continue 'a; }) { () } \<rbrakk>"))
\<close>

subsection\<open>Loop Control: Elaboration\<close>

context
  fixes n m :: nat
    and c :: bool
    and v :: \<open>32 word\<close>
    and xs :: \<open>32 word list\<close>
    and x :: \<open>32 word option\<close>
    and B :: \<open>('s, unit, 'r, 'abort, 'i, 'o) expression\<close>
begin

\<comment>\<open>Loops followed by further statements without a semicolon\<close>
lemma \<open>\<lbrakk> for i in (\<llangle>xs\<rrangle>) { if \<llangle>c\<rrangle> { break; } } \<epsilon>\<open>B\<close> \<rbrakk>
         = sequence (for_loop None (funcall1 into_iter (literal xs))
             (\<lambda>i. two_armed_conditional (literal c) (loop_break None) skip)) B\<close>
  by (rule refl)

lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while (\<llangle>c\<rrangle>) { continue; } \<epsilon>\<open>B\<close> \<rbrakk>
         = sequence (bounded_while None n (literal c) (loop_continue None)) B\<close>
  by (rule refl)

lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { break; } \<epsilon>\<open>B\<close> \<rbrakk>
         = sequence (bounded_while None n (literal True) (loop_break None)) B\<close>
  by (rule refl)

lemma \<open>\<lbrakk> 'a: for i in (\<llangle>xs\<rrangle>) { if \<llangle>c\<rrangle> { continue 'a; } } \<epsilon>\<open>B\<close> \<rbrakk>
         = sequence (for_loop (Some STR ''a'') (funcall1 into_iter (literal xs))
             (\<lambda>i. two_armed_conditional (literal c) (loop_continue (Some STR ''a'')) skip))
             B\<close>
  by (rule refl)

lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: while (\<llangle>c\<rrangle>) { break 'a; } \<epsilon>\<open>B\<close> \<rbrakk>
         = sequence (bounded_while (Some STR ''a'') n (literal c) (loop_break (Some STR ''a''))) B\<close>
  by (rule refl)

lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { continue 'a; } \<epsilon>\<open>B\<close> \<rbrakk>
         = sequence (bounded_while (Some STR ''a'') n (literal True) (loop_continue (Some STR ''a''))) B\<close>
  by (rule refl)

\<comment>\<open>A labeled \<^verbatim>\<open>while let\<close> elaborates like the unlabeled one, except for the label\<close>
schematic_goal \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: while let Some(u) = \<llangle>x\<rrangle> { \<epsilon>\<open>B\<close> } \<rbrakk>
         = bounded_while (Some STR ''a'') n ?C skip
     \<and> \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let Some(u) = \<llangle>x\<rrangle> { \<epsilon>\<open>B\<close> } \<rbrakk> = bounded_while None n ?C skip\<close>
  by (rule conjI refl)+

schematic_goal \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: while let Some(u) = \<llangle>x\<rrangle> { \<epsilon>\<open>B\<close> } \<epsilon>\<open>B\<close> \<rbrakk>
         = sequence (bounded_while (Some STR ''a'') n ?C skip) B
     \<and> \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let Some(u) = \<llangle>x\<rrangle> { \<epsilon>\<open>B\<close> } \<epsilon>\<open>B\<close> \<rbrakk>
         = sequence (bounded_while None n ?C skip) B\<close>
  by (rule conjI refl)+

schematic_goal \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: while let (p, q) = (\<llangle>v\<rrangle>, \<llangle>c\<rrangle>) { \<epsilon>\<open>B\<close> } \<epsilon>\<open>B\<close> \<rbrakk>
         = sequence (bounded_while (Some STR ''a'') n ?C skip) B
     \<and> \<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while let (p, q) = (\<llangle>v\<rrangle>, \<llangle>c\<rrangle>) { \<epsilon>\<open>B\<close> } \<epsilon>\<open>B\<close> \<rbrakk>
         = sequence (bounded_while None n ?C skip) B\<close>
  by (rule conjI refl)+

\<comment>\<open>Tuple pattern: the body, including a \<^verbatim>\<open>break\<close>, lies in the condition of the loop\<close>
lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: while let (p, q) = \<llangle>(v, c, TNil)\<rrangle> { if \<llangle>c\<rrangle> { break 'a; } } \<rbrakk>
         = bounded_while (Some STR ''a'') n
             (bind (literal (v, c, TNil)) (\<lambda>(p, q, _).
               sequence (two_armed_conditional (literal c) (loop_break (Some STR ''a'')) skip) (literal True)))
             skip\<close>
  by (rule refl)

\<comment>\<open>Shadowed labels: each loop keeps its own label\<close>
lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { #[fuel(\<epsilon>\<open>m\<close>)] 'a: loop { break 'a; } continue 'a; } \<rbrakk>
         = bounded_while (Some STR ''a'') n (literal True)
             (sequence (bounded_while (Some STR ''a'') m (literal True) (loop_break (Some STR ''a'')))
               (loop_continue (Some STR ''a'')))\<close>
  by (rule refl)

\<comment>\<open>A labeled \<^verbatim>\<open>break\<close> in the condition of an inner \<^verbatim>\<open>while\<close> may name an outer loop\<close>
lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'o: loop { #[fuel(\<epsilon>\<open>m\<close>)] while ({ break 'o; }) { () } } \<rbrakk>
         = bounded_while (Some STR ''o'') n (literal True)
             (bounded_while None m (loop_break (Some STR ''o'')) (literal ()))\<close>
  by (rule refl)

\<comment>\<open>An unlabeled \<^verbatim>\<open>break\<close> of a loop inside the condition of a \<^verbatim>\<open>while\<close> loop is allowed\<close>
lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while ({ #[fuel(\<epsilon>\<open>m\<close>)] loop { break; } \<llangle>c\<rrangle> }) { () } \<rbrakk>
         = bounded_while None n (sequence (bounded_while None m (literal True) (loop_break None)) (literal c))
             (literal ())\<close>
  by (rule refl)

\<comment>\<open>An unlabeled \<^verbatim>\<open>break\<close> in the iterator of a \<^verbatim>\<open>for\<close> loop belongs to the enclosing loop\<close>
lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { for i in (if \<llangle>c\<rrangle> { break; } else { \<llangle>xs\<rrangle> }) { () } } \<rbrakk>
         = bounded_while None n (literal True)
             (for_loop None (funcall1 into_iter (two_armed_conditional (literal c) (loop_break None) (literal xs)))
               (\<lambda>i. literal ()))\<close>
  by (rule refl)

\<comment>\<open>A closure inside a loop may contain its own loop with \<^verbatim>\<open>break\<close>\<close>
term \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { let f = ( || { #[fuel(\<epsilon>\<open>m\<close>)] loop { break; } } ); break; } \<rbrakk>\<close>

\<comment>\<open>A label may have the name of the loop variable or of a fixed variable\<close>
lemma \<open>\<lbrakk> 'i: for i in (\<llangle>xs\<rrangle>) { if \<llangle>c\<rrangle> { break 'i; } } \<rbrakk>
         = for_loop (Some STR ''i'') (funcall1 into_iter (literal xs))
             (\<lambda>i. two_armed_conditional (literal c) (loop_break (Some STR ''i'')) skip)\<close>
  by (rule refl)

lemma \<open>\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'n: loop { continue 'n; } \<rbrakk>
         = bounded_while (Some STR ''n'') n (literal True) (loop_continue (Some STR ''n''))\<close>
  by (rule refl)

\<comment>\<open>\<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> in \<^verbatim>\<open>match\<close>, \<^verbatim>\<open>if let\<close> and \<^verbatim>\<open>let else\<close>\<close>
term \<open>\<lbrakk>
  for i in (\<llangle>xs\<rrangle>) {
    match \<llangle>x\<rrangle> {
      Some(y) \<Rightarrow> { break; },
      None \<Rightarrow> { continue; }
    };
    if let Some(y) = \<llangle>x\<rrangle> { break; } else { continue; }
    let Some(y) = \<llangle>x\<rrangle> else { continue; };
    ()
  }
\<rbrakk>\<close>

end

subsection\<open>Loop Control: Rejected Programs\<close>

ML\<open>
  fun read_error ctxt s =
    (case Exn.result (Syntax.read_term ctxt) s of
      Exn.Res _ => NONE
    | Exn.Exn exn => SOME (Runtime.exn_message exn))
  fun check_accepted ctxt s =
    (case read_error ctxt s of
      NONE => ()
    | SOME msg => error ("Rejected: " ^ s ^ "\n" ^ msg))
  fun check_rejected ctxt expected s =
    (case read_error ctxt s of
      NONE => error ("Accepted: " ^ s)
    | SOME msg =>
        if String.isSubstring expected msg then ()
        else error ("Rejected with another error: " ^ s ^ "\n" ^ msg))
  \<comment>\<open>A rejected program and an accepted program that differs from it only in its loop control\<close>
  fun check_pair ctxt expected (bad, good) =
    (check_rejected ctxt expected bad; check_accepted ctxt good)
\<close>

context
  fixes n m :: nat
    and c :: bool
    and xs :: \<open>32 word list\<close>
    and x :: \<open>32 word option\<close>
begin

ML_val\<open>
  val ctxt = \<^context>
  val outside_break = "uRust: break outside of a loop"
  val outside_continue = "uRust: continue outside of a loop"
  val cond_break = "uRust: break without a label in the condition of a while loop"
  val cond_continue = "uRust: continue without a label in the condition of a while loop"
  fun unknown what l = "uRust: " ^ what ^ " with unknown label '" ^ l

  \<comment>\<open>Outside of a loop\<close>
  val _ = check_pair ctxt outside_break
    ("\<lbrakk> break; \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { break; } \<rbrakk>")
  val _ = check_pair ctxt outside_continue
    ("\<lbrakk> if \<llangle>c\<rrangle> { continue; } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { if \<llangle>c\<rrangle> { continue; } } \<rbrakk>")

  \<comment>\<open>After a loop, in the sequence forms (the statement after the loop is outside of it)\<close>
  val _ = check_pair ctxt outside_break
    ("\<lbrakk> for i in (\<llangle>xs\<rrangle>) { () } break; \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { for i in (\<llangle>xs\<rrangle>) { () } break; } \<rbrakk>")
  val _ = check_pair ctxt outside_continue
    ("\<lbrakk> #[fuel(\<epsilon>\<open>m\<close>)] while (\<llangle>c\<rrangle>) { () } continue; \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { #[fuel(\<epsilon>\<open>m\<close>)] while (\<llangle>c\<rrangle>) { () } continue; } \<rbrakk>")
  val _ = check_pair ctxt outside_break
    ("\<lbrakk> #[fuel(\<epsilon>\<open>m\<close>)] loop { () } break; \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { #[fuel(\<epsilon>\<open>m\<close>)] loop { () } break; } \<rbrakk>")
  val _ = check_pair ctxt outside_break
    ("\<lbrakk> #[fuel(\<epsilon>\<open>m\<close>)] while let Some(y) = \<llangle>x\<rrangle> { () } break; \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { #[fuel(\<epsilon>\<open>m\<close>)] while let Some(y) = \<llangle>x\<rrangle> { () } break; } \<rbrakk>")

  \<comment>\<open>The label of a labeled loop is not in scope after the loop (sequence forms)\<close>
  val _ = check_pair ctxt (unknown "break" "b")
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { 'b: for i in (\<llangle>xs\<rrangle>) { () } break 'b; } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { 'b: for i in (\<llangle>xs\<rrangle>) { () } break 'a; } \<rbrakk>")
  val _ = check_pair ctxt (unknown "continue" "b")
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { #[fuel(\<epsilon>\<open>m\<close>)] 'b: while (\<llangle>c\<rrangle>) { () } continue 'b; } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { #[fuel(\<epsilon>\<open>m\<close>)] 'b: while (\<llangle>c\<rrangle>) { () } continue 'a; } \<rbrakk>")
  val _ = check_pair ctxt (unknown "break" "b")
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { #[fuel(\<epsilon>\<open>m\<close>)] 'b: loop { () } break 'b; } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { #[fuel(\<epsilon>\<open>m\<close>)] 'b: loop { () } break 'a; } \<rbrakk>")
  val _ = check_pair ctxt (unknown "break" "b")
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { #[fuel(\<epsilon>\<open>m\<close>)] 'b: while let Some(y) = \<llangle>x\<rrangle> { () } break 'b; } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { #[fuel(\<epsilon>\<open>m\<close>)] 'b: while let Some(y) = \<llangle>x\<rrangle> { () } break 'a; } \<rbrakk>")

  \<comment>\<open>Unknown labels\<close>
  val _ = check_pair ctxt (unknown "break" "b")
    ("\<lbrakk> 'a: for i in (\<llangle>xs\<rrangle>) { break 'b; } \<rbrakk>",
     "\<lbrakk> 'a: for i in (\<llangle>xs\<rrangle>) { break 'a; } \<rbrakk>")
  val _ = check_pair ctxt (unknown "continue" "b")
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: while let Some(y) = \<llangle>x\<rrangle> { continue 'b; } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: while let Some(y) = \<llangle>x\<rrangle> { continue 'a; } \<rbrakk>")
  val _ = check_pair ctxt (unknown "continue" "a")
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { continue 'a; } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { continue 'a; } \<rbrakk>")

  \<comment>\<open>The label of a \<^verbatim>\<open>for\<close> loop is not in scope in its iterator expression\<close>
  val _ = check_pair ctxt (unknown "break" "a")
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'o: loop { 'a: for i in (if \<llangle>c\<rrangle> { break 'a; } else { \<llangle>xs\<rrangle> }) { () } } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'o: loop { 'a: for i in (if \<llangle>c\<rrangle> { break 'o; } else { \<llangle>xs\<rrangle> }) { () } } \<rbrakk>")
  \<comment>\<open>An unlabeled \<^verbatim>\<open>break\<close> there needs an enclosing loop\<close>
  val _ = check_pair ctxt outside_break
    ("\<lbrakk> for i in (if \<llangle>c\<rrangle> { break; } else { \<llangle>xs\<rrangle> }) { () } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { for i in (if \<llangle>c\<rrangle> { break; } else { \<llangle>xs\<rrangle> }) { () } } \<rbrakk>")

  \<comment>\<open>Unlabeled \<^verbatim>\<open>break\<close> and \<^verbatim>\<open>continue\<close> in the condition of a \<^verbatim>\<open>while\<close> loop, also
     inside an enclosing loop\<close>
  val _ = check_pair ctxt cond_break
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'o: loop { #[fuel(\<epsilon>\<open>m\<close>)] while ({ break; }) { () } } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'o: loop { #[fuel(\<epsilon>\<open>m\<close>)] while ({ break 'o; }) { () } } \<rbrakk>")
  val _ = check_pair ctxt cond_continue
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'w: while ({ if \<llangle>c\<rrangle> { continue; } \<llangle>c\<rrangle> }) { () } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'w: while ({ if \<llangle>c\<rrangle> { continue 'w; } \<llangle>c\<rrangle> }) { () } \<rbrakk>")
  \<comment>\<open>... and in the scrutinee of a \<^verbatim>\<open>while let\<close> loop, with a non-tuple and a tuple pattern\<close>
  val _ = check_pair ctxt cond_continue
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'w: while let Some(y) = (if \<llangle>c\<rrangle> { continue; } else { \<llangle>x\<rrangle> }) { () } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'w: while let Some(y) = (if \<llangle>c\<rrangle> { continue 'w; } else { \<llangle>x\<rrangle> }) { () } \<rbrakk>")
  val _ = check_pair ctxt cond_break
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'w: while let (p, q) = (if \<llangle>c\<rrangle> { break; } else { \<llangle>(c, c, TNil)\<rrangle> }) { () } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'w: while let (p, q) = (if \<llangle>c\<rrangle> { break 'w; } else { \<llangle>(c, c, TNil)\<rrangle> }) { () } \<rbrakk>")
  \<comment>\<open>... but not in the body of a loop inside the condition\<close>
  val _ = check_pair ctxt cond_break
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while ({ \<llangle>c\<rrangle>; break; }) { () } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] while ({ #[fuel(\<epsilon>\<open>m\<close>)] loop { break; } \<llangle>c\<rrangle> }) { () } \<rbrakk>")

  \<comment>\<open>Closures are separate function bodies, also in a loop condition\<close>
  val _ = check_pair ctxt outside_continue
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { let f = ( || { continue; } ); break; } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] loop { let f = ( || { #[fuel(\<epsilon>\<open>m\<close>)] loop { continue; } } ); break; } \<rbrakk>")
  val _ = check_pair ctxt (unknown "continue" "a")
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { let f = ( |y| { #[fuel(\<epsilon>\<open>m\<close>)] loop { continue 'a; } } ); break; } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'a: loop { let f = ( |y| { #[fuel(\<epsilon>\<open>m\<close>)] 'a: loop { continue 'a; } } ); break; } \<rbrakk>")
  val _ = check_pair ctxt outside_break
    ("\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'w: while ({ let f = ( || { break; } ); \<llangle>c\<rrangle> }) { () } \<rbrakk>",
     "\<lbrakk> #[fuel(\<epsilon>\<open>n\<close>)] 'w: while ({ let f = ( || { #[fuel(\<epsilon>\<open>m\<close>)] loop { break; } } ); \<llangle>c\<rrangle> }) { () } \<rbrakk>")
\<close>

end

end
