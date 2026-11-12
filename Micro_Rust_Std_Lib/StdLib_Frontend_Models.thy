(*<*)
theory StdLib_Frontend_Models
  imports Crush.Crush StdLib_References StdLib_Ordering Misc.Result "HOL-Library.Sublist" "Word_Lib.Word_Lib_Sumo"
begin
(*>*)

section\<open>Models of standard library functions for translated Rust\<close>

text\<open>
  The Rust frontend (urust-frontend) translates a call of some Rust standard library functions to a
  call of a model of the function. The models below are written by hand: Rust's own definitions are
  not translated yet, and this library has no counterpart for them. A Rust \<^verbatim>\<open>Vec<T>\<close> and a
  slice \<^verbatim>\<open>[T]\<close> are values of type @{typ \<open>'v list\<close>} (their elements); a \<^verbatim>\<open>&mut\<close>
  reference to one is a reference to such a list.
\<close>

text\<open>\<^verbatim>\<open>alloc::vec::from_elem(elem, n)\<close> (the expansion of \<^verbatim>\<open>vec![elem; n]\<close>): \<open>n\<close> copies of
  \<open>elem\<close>.\<close>
definition vec_from_elem :: \<open>'v \<Rightarrow> 64 word \<Rightarrow> ('s, 'v list, 'abort, 'i, 'o) function_body\<close> where
  \<open>vec_from_elem x n \<equiv> FunctionBody (literal (replicate (unat n) x))\<close>

definition vec_from_elem_contract :: \<open>'v \<Rightarrow> 64 word \<Rightarrow> ('s::sepalg, 'v list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>vec_from_elem_contract x n \<equiv>
     let pre = emp in
     let post = \<lambda>r. \<langle>r = replicate (unat n) x\<rangle> in
       make_function_contract pre post\<close>

lemma vec_from_elem_spec [crush_specs]:
  shows \<open>\<Gamma> ; vec_from_elem x n \<Turnstile>\<^sub>F vec_from_elem_contract x n\<close>
  by (crush_boot f: vec_from_elem_def contract: vec_from_elem_contract_def) crush_base

section\<open>Iterators\<close>

text\<open>
  A standard library iterator is represented by its state; its \<^verbatim>\<open>next\<close> is a step function
  from a state to the next item (if any) and the new state.
\<close>

type_synonym ('r, 's, 'v, 'abort, 'i, 'o) iter_step =
  \<open>'r \<Rightarrow> ('s, 'v option \<times> 'r \<times> tnil, 'abort, 'i, 'o) function_body\<close>

text\<open>An iterator over the elements of a list (\<^verbatim>\<open>slice::Iter\<close>, \<^verbatim>\<open>str::Lines\<close>, ...): its state is
  the list of the remaining elements.\<close>
definition list_iter_next :: \<open>('v list, 's, 'v, 'abort, 'i, 'o) iter_step\<close> where
  \<open>list_iter_next xs \<equiv> FunctionBody (literal (case xs of
       [] \<Rightarrow> (None, [], TNil)
     | x # r \<Rightarrow> (Some x, r, TNil)))\<close>

definition list_iter_next_back :: \<open>('v list, 's, 'v, 'abort, 'i, 'o) iter_step\<close> where
  \<open>list_iter_next_back xs \<equiv> FunctionBody (literal (if xs = [] then (None, [], TNil)
     else (Some (last xs), butlast xs, TNil)))\<close>

text\<open>\<^verbatim>\<open>Enumerate<I>\<close>: the state of \<^verbatim>\<open>I\<close> and the count.\<close>
definition enumerate_next :: \<open>('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow>
    ('r \<times> 64 word \<times> tnil, 's, 64 word \<times> 'v \<times> tnil, 'abort, 'i, 'o) iter_step\<close> where
  \<open>enumerate_next nv st \<equiv> FunctionBody \<lbrakk>
     let it = st.0;
     let c = st.1;
     let res = nv(it);
     let it2 = res.1;
     match res.0 {
       None \<Rightarrow> (None, (it2, c)),
       Some(a) \<Rightarrow> {
         let c2 = c + 1_usize;
         (Some((c, a)), (it2, c2))
       }
     }
  \<rbrakk>\<close>


text\<open>\<^verbatim>\<open>Zip<A, B>\<close>: the states of \<^verbatim>\<open>A\<close> and \<^verbatim>\<open>B\<close>; as Rust's general \<^verbatim>\<open>Zip::next\<close>,
  \<^verbatim>\<open>B\<close> is advanced only if \<^verbatim>\<open>A\<close> has an item.\<close>
definition zip_next :: \<open>('ra, 's, 'a, 'abort, 'i, 'o) iter_step \<Rightarrow> ('rb, 's, 'b, 'abort, 'i, 'o) iter_step \<Rightarrow>
    ('ra \<times> 'rb \<times> tnil, 's, 'a \<times> 'b \<times> tnil, 'abort, 'i, 'o) iter_step\<close> where
  \<open>zip_next na nb st \<equiv> FunctionBody \<lbrakk>
     let ra = na(st.0);
     match ra.0 {
       None \<Rightarrow> (None, (ra.1, st.1)),
       Some(x) \<Rightarrow> {
         let rb = nb(st.1);
         match rb.0 {
           None \<Rightarrow> (None, (ra.1, rb.1)),
           Some(y) \<Rightarrow> (Some((x, y)), (ra.1, rb.1))
         }
       }
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Iterator::nth\<close> (the default method): \<open>k\<close> calls of \<^verbatim>\<open>next\<close> that stop at the first
  \<^verbatim>\<open>None\<close>, then one more.\<close>
fun iter_nth_nat :: \<open>('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow> nat \<Rightarrow> ('r, 's, 'v, 'abort, 'i, 'o) iter_step\<close> where
  \<open>iter_nth_nat nv 0 st = nv st\<close>
| \<open>iter_nth_nat nv (Suc k) st = FunctionBody \<lbrakk>
     let r = nv(st);
     match r.0 {
       None \<Rightarrow> (None, r.1),
       Some(_) \<Rightarrow> {
         let g = \<llangle>iter_nth_nat nv k\<rrangle>;
         g(r.1)
       }
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Skip<I>\<close>: the state of \<^verbatim>\<open>I\<close> and the number of items still to skip.\<close>
definition skip_next :: \<open>('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow>
    ('r \<times> 64 word \<times> tnil, 's, 'v, 'abort, 'i, 'o) iter_step\<close> where
  \<open>skip_next nv st \<equiv> FunctionBody \<lbrakk>
     if st.1 > 0_usize {
       let g = \<llangle>iter_nth_nat nv (unat (fst (snd st)))\<rrangle>;
       let r = g(st.0);
       (r.0, (r.1, 0_usize))
     } else {
       let r = nv(st.0);
       (r.0, (r.1, 0_usize))
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Take<I>\<close>: the state of \<^verbatim>\<open>I\<close> and the number of items still to yield.\<close>
definition take_next :: \<open>('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow>
    ('r \<times> 64 word \<times> tnil, 's, 'v, 'abort, 'i, 'o) iter_step\<close> where
  \<open>take_next nv st \<equiv> FunctionBody \<lbrakk>
     if st.1 != 0_usize {
       let n = st.1 - 1_usize;
       let r = nv(st.0);
       (r.0, (r.1, n))
     } else {
       (None, st)
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>TakeWhile<I, P>\<close>: the state of \<^verbatim>\<open>I\<close>, the flag (an item failed the predicate) and the
  predicate.\<close>
definition take_while_next :: \<open>('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow>
    ('r \<times> bool \<times> ('v \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body) \<times> tnil, 's, 'v, 'abort, 'i, 'o) iter_step\<close> where
  \<open>take_while_next nv st \<equiv> FunctionBody \<lbrakk>
     let p = st.2;
     if st.1 {
       (None, st)
     } else {
       let r = nv(st.0);
       match r.0 {
         None \<Rightarrow> (None, (r.1, False, p)),
         Some(x) \<Rightarrow> {
           if p(x) {
             (Some(x), (r.1, False, p))
           } else {
             (None, (r.1, True, p))
           }
         }
       }
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Map<I, F>\<close>: the state of \<^verbatim>\<open>I\<close> and the function.\<close>
definition map_next :: \<open>('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow>
    ('r \<times> ('v \<Rightarrow> ('s, 'w, 'abort, 'i, 'o) function_body) \<times> tnil, 's, 'w, 'abort, 'i, 'o) iter_step\<close> where
  \<open>map_next nv st \<equiv> FunctionBody \<lbrakk>
     let f = st.1;
     let r = nv(st.0);
     match r.0 {
       None \<Rightarrow> (None, (r.1, f)),
       Some(x) \<Rightarrow> (Some(f(x)), (r.1, f))
     }
  \<rbrakk>\<close>

subsection\<open>Consuming an iterator\<close>

text\<open>The methods that run an iterator to its end take the fuel of the translated crate: they panic
  when it runs out, like the crate's recursive functions.\<close>

fun iter_fold :: \<open>nat \<Rightarrow> ('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow>
    ('a0 \<Rightarrow> 'v \<Rightarrow> ('s, 'a0, 'abort, 'i, 'o) function_body) \<Rightarrow> 'r \<Rightarrow> 'a0 \<Rightarrow>
    ('s, 'a0, 'abort, 'i, 'o) function_body\<close> where
  \<open>iter_fold 0 nv f st a0 = FunctionBody \<lbrakk> panic!("out of fuel") \<rbrakk>\<close>
| \<open>iter_fold (Suc n) nv f st a0 = FunctionBody \<lbrakk>
     let r = nv(st);
     match r.0 {
       None \<Rightarrow> a0,
       Some(x) \<Rightarrow> {
         let a2 = f(a0, x);
         let g = \<llangle>iter_fold n nv f\<rrangle>;
         g(r.1, a2)
       }
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Iterator::count\<close>: with Rust's overflow check of the count.\<close>
definition iter_count :: \<open>nat \<Rightarrow> ('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow> 'r \<Rightarrow>
    ('s, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>iter_count fuel nv st \<equiv> iter_fold fuel nv (\<lambda>c _. FunctionBody \<lbrakk> c + 1_usize \<rbrakk>) st 0\<close>

text\<open>\<^verbatim>\<open>Iterator::collect\<close> into a \<^verbatim>\<open>Vec\<close>: the items in order.\<close>
definition iter_collect_list :: \<open>nat \<Rightarrow> ('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow> 'r \<Rightarrow>
    ('s, 'v list, 'abort, 'i, 'o) function_body\<close> where
  \<open>iter_collect_list fuel nv st \<equiv> iter_fold fuel nv (\<lambda>xs x. FunctionBody (literal (xs @ [x]))) st []\<close>

section\<open>Strings\<close>

text\<open>A \<^verbatim>\<open>str\<close> is a @{typ String.literal}, whose characters are ASCII.\<close>

definition strip_cr :: \<open>char list \<Rightarrow> char list\<close> where
  \<open>strip_cr l \<equiv> if l \<noteq> [] \<and> last l = CHR 0x0D then butlast l else l\<close>

text\<open>\<^verbatim>\<open>str::lines\<close>: \<^verbatim>\<open>split_inclusive('\n')\<close>, each piece without its \<^verbatim>\<open>\n\<close> and then
  without a \<^verbatim>\<open>\r\<close> before it.\<close>
fun lines_aux :: \<open>char list \<Rightarrow> char list \<Rightarrow> char list list\<close> where
  \<open>lines_aux cur [] = (if cur = [] then [] else [cur])\<close>
| \<open>lines_aux cur (c # cs) = (if c = CHR 0x0A then strip_cr cur # lines_aux [] cs else lines_aux (cur @ [c]) cs)\<close>

definition str_lines :: \<open>String.literal \<Rightarrow> ('s, String.literal list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_lines s \<equiv> FunctionBody (literal (List.map String.implode (lines_aux [] (String.explode s))))\<close>

text\<open>\<^verbatim>\<open>char::is_whitespace\<close> on ASCII characters (Unicode \<open>White_Space\<close>).\<close>
definition ascii_whitespace :: \<open>char \<Rightarrow> bool\<close> where
  \<open>ascii_whitespace c \<equiv> of_char c \<in> {9, 10, 11, 12, 13, 32::nat}\<close>

fun words_aux :: \<open>char list \<Rightarrow> char list \<Rightarrow> char list list\<close> where
  \<open>words_aux cur [] = (if cur = [] then [] else [cur])\<close>
| \<open>words_aux cur (c # cs) = (if ascii_whitespace c then (if cur = [] then words_aux [] cs else cur # words_aux [] cs)
     else words_aux (cur @ [c]) cs)\<close>

text\<open>\<^verbatim>\<open>str::split_whitespace\<close>: the maximal non-empty runs of non-whitespace characters.\<close>
definition str_split_whitespace :: \<open>String.literal \<Rightarrow> ('s, String.literal list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_split_whitespace s \<equiv> FunctionBody (literal (List.map String.implode (words_aux [] (String.explode s))))\<close>

definition str_starts_with_char :: \<open>String.literal \<Rightarrow> char \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_starts_with_char s c \<equiv> FunctionBody (literal (String.explode s \<noteq> [] \<and> hd (String.explode s) = c))\<close>

definition str_starts_with_str :: \<open>String.literal \<Rightarrow> String.literal \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_starts_with_str s p \<equiv> FunctionBody (literal (prefix (String.explode p) (String.explode s)))\<close>

definition str_as_bytes :: \<open>String.literal \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_as_bytes s \<equiv> FunctionBody (literal (List.map (of_nat \<circ> of_char) (String.explode s)))\<close>

subsection\<open>Parsing integers\<close>

text\<open>\<^verbatim>\<open>core::num::IntErrorKind\<close>; a \<^verbatim>\<open>ParseIntError\<close> is its only field.\<close>
datatype int_error_kind = IntErrorKind_Empty | IntErrorKind_InvalidDigit | IntErrorKind_PosOverflow
  | IntErrorKind_NegOverflow | IntErrorKind_Zero

text\<open>The decimal digits after the sign, as \<^verbatim>\<open>from_str_radix\<close>: a character that is not a digit is
  an error before the overflow of the value accumulated so far.\<close>
fun parse_digits :: \<open>bool \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> char list \<Rightarrow> (int, int_error_kind) result\<close> where
  \<open>parse_digits neg lo hi a [] = Ok a\<close>
| \<open>parse_digits neg lo hi a (c # cs) =
     (if \<not> (48 \<le> (of_char c :: nat) \<and> (of_char c :: nat) \<le> 57) then Err IntErrorKind_InvalidDigit
      else let d = int (of_char c :: nat) - 48; a' = (if neg then a * 10 - d else a * 10 + d) in
        if neg \<and> a' < lo then Err IntErrorKind_NegOverflow
        else if \<not> neg \<and> hi < a' then Err IntErrorKind_PosOverflow
        else parse_digits neg lo hi a' cs)\<close>

definition parse_int :: \<open>bool \<Rightarrow> int \<Rightarrow> int \<Rightarrow> char list \<Rightarrow> (int, int_error_kind) result\<close> where
  \<open>parse_int sg lo hi s \<equiv> (case s of
      [] \<Rightarrow> Err IntErrorKind_Empty
    | c # r \<Rightarrow> if (c = CHR ''+'' \<or> c = CHR ''-'') \<and> r = [] then Err IntErrorKind_InvalidDigit
        else if c = CHR ''+'' then parse_digits False lo hi 0 r
        else if c = CHR ''-'' \<and> sg then parse_digits True lo hi 0 r
        else parse_digits False lo hi 0 s)\<close>

text\<open>\<^verbatim>\<open>str::parse\<close> into an unsigned and into a signed integer type.\<close>
definition str_parse_word :: \<open>String.literal \<Rightarrow> ('s, ('l::len word, int_error_kind) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_parse_word s \<equiv> FunctionBody (literal (case parse_int False 0 (2 ^ LENGTH('l) - 1) (String.explode s) of
     Ok n \<Rightarrow> Ok (word_of_int n) | Err e \<Rightarrow> Err e))\<close>

definition str_parse_sword :: \<open>String.literal \<Rightarrow> ('s, ('l::len sword, int_error_kind) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_parse_sword s \<equiv> FunctionBody (literal (case parse_int True (- (2 ^ (LENGTH('l) - 1))) (2 ^ (LENGTH('l) - 1) - 1) (String.explode s) of
     Ok n \<Rightarrow> Ok (word_of_int n) | Err e \<Rightarrow> Err e))\<close>

section\<open>Option and Result\<close>

definition option_unwrap_or :: \<open>'v option \<Rightarrow> 'v \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>option_unwrap_or opt d \<equiv> FunctionBody (literal (case opt of Some x \<Rightarrow> x | None \<Rightarrow> d))\<close>

definition option_map :: \<open>'v option \<Rightarrow> ('v \<Rightarrow> ('s, 'w, 'abort, 'i, 'o) function_body) \<Rightarrow> ('s, 'w option, 'abort, 'i, 'o) function_body\<close> where
  \<open>option_map opt f \<equiv> FunctionBody \<lbrakk>
     match opt { None \<Rightarrow> None, Some(x) \<Rightarrow> Some(f(x)) }
  \<rbrakk>\<close>

definition option_and_then :: \<open>'v option \<Rightarrow> ('v \<Rightarrow> ('s, 'w option, 'abort, 'i, 'o) function_body) \<Rightarrow> ('s, 'w option, 'abort, 'i, 'o) function_body\<close> where
  \<open>option_and_then opt f \<equiv> FunctionBody \<lbrakk>
     match opt { None \<Rightarrow> None, Some(x) \<Rightarrow> f(x) }
  \<rbrakk>\<close>

definition option_ok_or_else :: \<open>'v option \<Rightarrow> ('s, 'e, 'abort, 'i, 'o) function_body \<Rightarrow> ('s, ('v, 'e) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>option_ok_or_else opt f \<equiv> FunctionBody \<lbrakk>
     match opt { Some(x) \<Rightarrow> Ok(x), None \<Rightarrow> Err(f()) }
  \<rbrakk>\<close>

definition option_unwrap_or_else :: \<open>'v option \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>option_unwrap_or_else opt f \<equiv> FunctionBody \<lbrakk>
     match opt { Some(x) \<Rightarrow> x, None \<Rightarrow> f() }
  \<rbrakk>\<close>

definition result_map :: \<open>('v, 'e) result \<Rightarrow> ('v \<Rightarrow> ('s, 'w, 'abort, 'i, 'o) function_body) \<Rightarrow> ('s, ('w, 'e) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_map r f \<equiv> FunctionBody \<lbrakk>
     match r { Ok(x) \<Rightarrow> Ok(f(x)), Err(e) \<Rightarrow> Err(e) }
  \<rbrakk>\<close>

definition result_map_err :: \<open>('v, 'e) result \<Rightarrow> ('e \<Rightarrow> ('s, 'f, 'abort, 'i, 'o) function_body) \<Rightarrow> ('s, ('v, 'f) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_map_err r f \<equiv> FunctionBody \<lbrakk>
     match r { Ok(x) \<Rightarrow> Ok(x), Err(e) \<Rightarrow> Err(f(e)) }
  \<rbrakk>\<close>

section\<open>Slices and vectors (values)\<close>

definition slice_get :: \<open>'v list \<Rightarrow> 64 word \<Rightarrow> ('s, 'v option, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_get xs i \<equiv> FunctionBody (literal (if unat i < length xs then Some (xs ! unat i) else None))\<close>

definition slice_first :: \<open>'v list \<Rightarrow> ('s, 'v option, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_first xs \<equiv> FunctionBody (literal (case xs of [] \<Rightarrow> None | x # _ \<Rightarrow> Some x))\<close>

definition slice_last :: \<open>'v list \<Rightarrow> ('s, 'v option, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_last xs \<equiv> FunctionBody (literal (if xs = [] then None else Some (last xs)))\<close>

definition slice_is_empty :: \<open>'v list \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_is_empty xs \<equiv> FunctionBody (literal (xs = []))\<close>

text\<open>\<^verbatim>\<open><[T]>::chunks_exact(size)\<close>: panics if \<open>size\<close> is 0; the chunks of \<open>size\<close> elements, and
  the remainder (shorter than \<open>size\<close>).\<close>
fun chunks_of :: \<open>nat \<Rightarrow> 'v list \<Rightarrow> 'v list list\<close> where
  \<open>chunks_of n xs = (if n = 0 \<or> length xs < n then [] else take n xs # chunks_of n (drop n xs))\<close>

definition slice_chunks_exact :: \<open>'v list \<Rightarrow> 64 word \<Rightarrow> ('s, 'v list list \<times> 'v list \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_chunks_exact xs n \<equiv> FunctionBody \<lbrakk>
     if n == 0_usize { panic!("chunk size must be non-zero") };
     \<llangle>(chunks_of (unat n) xs, drop (length xs - length xs mod unat n) xs, TNil)\<rrangle>
  \<rbrakk>\<close>

section\<open>Integers\<close>

definition wrapping_add :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>wrapping_add a b \<equiv> FunctionBody (literal (a + b))\<close>
definition wrapping_sub :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>wrapping_sub a b \<equiv> FunctionBody (literal (a - b))\<close>
definition wrapping_mul :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>wrapping_mul a b \<equiv> FunctionBody (literal (a * b))\<close>

definition overflowing_sub :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word \<times> bool \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>overflowing_sub a b \<equiv> FunctionBody (literal (a - b, a < b, TNil))\<close>

definition checked_sub :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s, 'l word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>checked_sub a b \<equiv> FunctionBody (literal (if b \<le> a then Some (a - b) else None))\<close>

text\<open>\<^verbatim>\<open>checked_shl(rhs: u32)\<close>: \<^verbatim>\<open>None\<close> if \<open>rhs\<close> is at least the width.\<close>
definition checked_shl :: \<open>'l::len word \<Rightarrow> 32 word \<Rightarrow> ('s, 'l word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>checked_shl a n \<equiv> FunctionBody (literal (if unat n < LENGTH('l) then Some (push_bit (unat n) a) else None))\<close>

definition trailing_zeros :: \<open>'l::len word \<Rightarrow> ('s, 32 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>trailing_zeros a \<equiv> FunctionBody (literal (of_nat (word_ctz a)))\<close>

definition leading_zeros :: \<open>'l::len word \<Rightarrow> ('s, 32 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>leading_zeros a \<equiv> FunctionBody (literal (of_nat (word_clz a)))\<close>

text\<open>\<^verbatim>\<open>from_be_bytes\<close>, \<^verbatim>\<open>to_be_bytes\<close> and the little-endian ones (also the native-endian
  ones: the frontend assumes a little-endian 64-bit platform).\<close>
definition from_be_bytes :: \<open>8 word list \<Rightarrow> ('s, 'l::len word, 'abort, 'i, 'o) function_body\<close> where
  \<open>from_be_bytes bs \<equiv> FunctionBody (literal (word_rcat bs))\<close>
definition from_le_bytes :: \<open>8 word list \<Rightarrow> ('s, 'l::len word, 'abort, 'i, 'o) function_body\<close> where
  \<open>from_le_bytes bs \<equiv> FunctionBody (literal (word_rcat (rev bs)))\<close>
definition to_be_bytes :: \<open>'l::len word \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>to_be_bytes w \<equiv> FunctionBody (literal (word_rsplit w))\<close>
definition to_le_bytes :: \<open>'l::len word \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>to_le_bytes w \<equiv> FunctionBody (literal (rev (word_rsplit w)))\<close>

text\<open>\<^verbatim>\<open>Ord::min\<close> and \<^verbatim>\<open>Ord::max\<close> (also \<^verbatim>\<open>cmp::min\<close>, \<^verbatim>\<open>cmp::max\<close>): \<^verbatim>\<open>min\<close> returns the
  first argument unless the second is smaller, \<^verbatim>\<open>max\<close> the second unless the first is larger.\<close>
definition ord_min :: \<open>'a::linorder \<Rightarrow> 'a \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close> where
  \<open>ord_min a b \<equiv> FunctionBody (literal (if a \<le> b then a else b))\<close>
definition ord_max :: \<open>'a::linorder \<Rightarrow> 'a \<Rightarrow> ('s, 'a, 'abort, 'i, 'o) function_body\<close> where
  \<open>ord_max a b \<equiv> FunctionBody (literal (if a \<le> b then b else a))\<close>

text\<open>\<^verbatim>\<open>ChunksExact<T>\<close>: the remaining chunks and the remainder.\<close>
definition chunks_exact_next :: \<open>('v list list \<times> 'v list \<times> tnil, 's, 'v list, 'abort, 'i, 'o) iter_step\<close> where
  \<open>chunks_exact_next st \<equiv> FunctionBody (literal (case fst st of
       [] \<Rightarrow> (None, st, TNil)
     | c # r \<Rightarrow> (Some c, (r, fst (snd st), TNil), TNil)))\<close>

text\<open>\<^verbatim>\<open>str::chars\<close>: the characters.\<close>
definition str_chars :: \<open>String.literal \<Rightarrow> ('s, char list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_chars s \<equiv> FunctionBody (literal (String.explode s))\<close>

text\<open>The write-back of a mutable borrow of the subslice of \<open>xs\<close> starting at \<open>lo\<close> (the frontend
  copies the subslice into a fresh mutable local and writes its final value \<open>ys\<close> back, which has
  the subslice's length): \<open>xs\<close> with the subslice replaced by \<open>ys\<close>.\<close>
definition slice_splice :: \<open>'v list \<Rightarrow> 64 word \<Rightarrow> 'v list \<Rightarrow> ('s, 'v list, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_splice xs lo ys \<equiv> FunctionBody (literal (take (unat lo) xs @ ys @ drop (unat lo + length ys) xs))\<close>

text\<open>\<^verbatim>\<open><[T]>::get\<close> by a range (\<^verbatim>\<open>a..b\<close>, \<^verbatim>\<open>a..=b\<close>, \<^verbatim>\<open>..b\<close>, \<^verbatim>\<open>..=b\<close>, \<^verbatim>\<open>a..\<close>,
  \<^verbatim>\<open>..\<close>; the last four by their only field): the subslice, \<^verbatim>\<open>None\<close> if the range is decreasing or
  exceeds the slice.\<close>
definition sublist_opt :: \<open>'v list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v list option\<close> where
  \<open>sublist_opt xs a b \<equiv> if a \<le> b \<and> b \<le> length xs then Some (take (b - a) (drop a xs)) else None\<close>

definition slice_get_range :: \<open>'v list \<Rightarrow> 64 word range \<Rightarrow> ('s, 'v list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_get_range xs r \<equiv> FunctionBody (literal (sublist_opt xs (unat (start r))
     (if end_inclusive r then unat (end r) + 1 else unat (end r))))\<close>
definition slice_get_to :: \<open>'v list \<Rightarrow> 64 word \<Rightarrow> ('s, 'v list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_get_to xs b \<equiv> FunctionBody (literal (sublist_opt xs 0 (unat b)))\<close>
definition slice_get_to_inclusive :: \<open>'v list \<Rightarrow> 64 word \<Rightarrow> ('s, 'v list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_get_to_inclusive xs b \<equiv> FunctionBody (literal (sublist_opt xs 0 (unat b + 1)))\<close>
definition slice_get_from :: \<open>'v list \<Rightarrow> 64 word \<Rightarrow> ('s, 'v list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_get_from xs a \<equiv> FunctionBody (literal (sublist_opt xs (unat a) (length xs)))\<close>
definition slice_get_full :: \<open>'v list \<Rightarrow> unit \<Rightarrow> ('s, 'v list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_get_full xs u \<equiv> FunctionBody (literal (Some xs))\<close>

text\<open>\<^verbatim>\<open>core::array::TryFromSliceError\<close>.\<close>
datatype try_from_slice_error = TryFromSliceError

text\<open>\<^verbatim>\<open>TryFrom<&[T]>\<close> for \<^verbatim>\<open>[T; N]\<close> (and for \<^verbatim>\<open>&[T; N]\<close>): \<^verbatim>\<open>Ok\<close> iff the slice has
  \<open>N\<close> elements.\<close>
definition slice_try_into_array :: \<open>'v list \<Rightarrow> 64 word \<Rightarrow> ('s, ('v list, try_from_slice_error) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_try_into_array xs n \<equiv> FunctionBody (literal (if length xs = unat n then Ok xs else Err TryFromSliceError))\<close>

text\<open>\<^verbatim>\<open><[T]>::copy_within(src, dest)\<close> on the list \<open>xs\<close>, for the range \<open>[a, b)\<close>: the list, if the
  range and the destination are within it.\<close>
definition copy_within_opt :: \<open>'v list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v list option\<close> where
  \<open>copy_within_opt xs a b d \<equiv> if a \<le> b \<and> b \<le> length xs \<and> d \<le> length xs - (b - a)
     then Some (take d xs @ take (b - a) (drop a xs) @ drop (d + (b - a)) xs) else None\<close>

text\<open>\<^verbatim>\<open>TryFrom<Vec<T>>\<close> for \<^verbatim>\<open>[T; N]\<close> (and \<^verbatim>\<open>Box<[T; N]>\<close>): \<^verbatim>\<open>Ok\<close> iff the vector has
  \<open>N\<close> elements, otherwise the vector is the error.\<close>
definition vec_try_into_array :: \<open>'v list \<Rightarrow> 64 word \<Rightarrow> ('s, ('v list, 'v list) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>vec_try_into_array xs n \<equiv> FunctionBody (literal (if length xs = unat n then Ok xs else Err xs))\<close>

definition option_is_some_and :: \<open>'v option \<Rightarrow> ('v \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body) \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>option_is_some_and opt f \<equiv> FunctionBody \<lbrakk>
     match opt { None \<Rightarrow> False, Some(x) \<Rightarrow> f(x) }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Vec::shrink_to_fit\<close>: it changes only the capacity, which the model does not have.\<close>
definition vec_shrink_to_fit :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>vec_shrink_to_fit ptr \<equiv> FunctionBody (literal ())\<close>

text\<open>\<^verbatim>\<open>Filter<I, P>\<close>: the state of \<^verbatim>\<open>I\<close> and the predicate; \<^verbatim>\<open>next\<close> is the inner
  \<^verbatim>\<open>find\<close>, which takes the crate's fuel (it panics when the fuel runs out).\<close>
fun filter_next :: \<open>nat \<Rightarrow> ('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow>
    ('r \<times> ('v \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body) \<times> tnil, 's, 'v, 'abort, 'i, 'o) iter_step\<close> where
  \<open>filter_next 0 nv st = FunctionBody \<lbrakk> panic!("out of fuel") \<rbrakk>\<close>
| \<open>filter_next (Suc n) nv st = FunctionBody \<lbrakk>
     let p = st.1;
     let r = nv(st.0);
     match r.0 {
       None \<Rightarrow> (None, (r.1, p)),
       Some(x) \<Rightarrow> {
         if p(x) {
           (\<llangle>Some x\<rrangle>, (r.1, p))
         } else {
           let g = \<llangle>filter_next n nv\<rrangle>;
           g((r.1, p))
         }
       }
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>slice::Chunks<T>\<close>: the remaining elements and the chunk size (the last chunk may be
  shorter).\<close>
definition chunks_next :: \<open>('v list \<times> 64 word \<times> tnil, 's, 'v list, 'abort, 'i, 'o) iter_step\<close> where
  \<open>chunks_next st \<equiv> FunctionBody (literal (case st of (xs, n, _) \<Rightarrow>
     if xs = [] then (None, st, TNil) else (Some (take (unat n) xs), (drop (unat n) xs, n, TNil), TNil)))\<close>

text\<open>\<^verbatim>\<open><[T]>::chunks(size)\<close>: panics if \<open>size\<close> is 0.\<close>
definition slice_chunks :: \<open>'v list \<Rightarrow> 64 word \<Rightarrow> ('s, 'v list \<times> 64 word \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>slice_chunks xs n \<equiv> FunctionBody \<lbrakk>
     if n == 0_usize { panic!("chunk size must be non-zero") };
     \<llangle>(xs, n, TNil)\<rrangle>
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>RangeFrom<T>\<close> of an unsigned integer as an iterator: its next value; panics on overflow
  (Rust's debug semantics).\<close>
definition range_from_next :: \<open>('l::len word, 's, 'l word, 'abort, 'i, 'o) iter_step\<close> where
  \<open>range_from_next st \<equiv> FunctionBody \<lbrakk>
     if \<llangle>st = - 1\<rrangle> { panic!("attempt to add with overflow") };
     \<llangle>(Some st, st + 1, TNil)\<rrangle>
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Iterator::any\<close>: stops at the first item satisfying the predicate; the result and
  the iterator's state after it.\<close>
fun iter_any_st :: \<open>nat \<Rightarrow> ('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow> ('v \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body) \<Rightarrow>
    'r \<Rightarrow> ('s, bool \<times> 'r \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>iter_any_st 0 nv f st = FunctionBody \<lbrakk> panic!("out of fuel") \<rbrakk>\<close>
| \<open>iter_any_st (Suc n) nv f st = FunctionBody \<lbrakk>
     let r = nv(st);
     match r.0 {
       None \<Rightarrow> (False, r.1),
       Some(x) \<Rightarrow> {
         if f(x) {
           (True, r.1)
         } else {
           let g = \<llangle>iter_any_st n nv f\<rrangle>;
           g(r.1)
         }
       }
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Iterator::min\<close> for items of a linear order (the unsigned integers): the first least
  item.\<close>
definition iter_min :: \<open>nat \<Rightarrow> ('r, 's, 'v::linorder, 'abort, 'i, 'o) iter_step \<Rightarrow> 'r \<Rightarrow>
    ('s, 'v option, 'abort, 'i, 'o) function_body\<close> where
  \<open>iter_min fuel nv st \<equiv> iter_fold fuel nv (\<lambda>m x. FunctionBody (literal (case m of
     None \<Rightarrow> Some x | Some y \<Rightarrow> if x < y then Some x else Some y))) st None\<close>

section\<open>Sorting and removing\<close>

text\<open>A comparison as Rust's \<^verbatim>\<open>Ord::cmp\<close> on a linear order.\<close>
definition ord_cmp :: \<open>'a::linorder \<Rightarrow> 'a \<Rightarrow> ordering\<close> where
  \<open>ord_cmp a b \<equiv> if a < b then Less else if a = b then Equal else Greater\<close>

text\<open>Lexicographic combination of comparisons (\<^verbatim>\<open>Ordering::then\<close>).\<close>
definition ordering_then :: \<open>ordering \<Rightarrow> ordering \<Rightarrow> ordering\<close> where
  \<open>ordering_then a b \<equiv> if a = Equal then b else a\<close>

text\<open>Stable insertion of \<open>x\<close> into a sorted list: after the elements not greater than it.\<close>
fun insort_by :: \<open>('v \<Rightarrow> 'v \<Rightarrow> ordering) \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v list\<close> where
  \<open>insort_by c x [] = [x]\<close>
| \<open>insort_by c x (y # ys) = (if c x y = Less then x # y # ys else y # insort_by c x ys)\<close>

text\<open>The stable sort by a comparison (the result of every stable sort for a total order).\<close>
definition sort_by :: \<open>('v \<Rightarrow> 'v \<Rightarrow> ordering) \<Rightarrow> 'v list \<Rightarrow> 'v list\<close> where
  \<open>sort_by c xs \<equiv> foldl (\<lambda>acc x. insort_by c x acc) [] xs\<close>

text\<open>\<^verbatim>\<open>Vec::dedup\<close> by structural equality: consecutive repeated elements removed.\<close>
fun dedup_list :: \<open>'v list \<Rightarrow> 'v list\<close> where
  \<open>dedup_list [] = []\<close>
| \<open>dedup_list [x] = [x]\<close>
| \<open>dedup_list (x # y # ys) = (if x = y then dedup_list (x # ys) else x # dedup_list (y # ys))\<close>

section\<open>Characters\<close>

text\<open>The UTF-8 encoding of a character (whose code point is below 256).\<close>
definition char_utf8 :: \<open>char \<Rightarrow> 8 word list\<close> where
  \<open>char_utf8 c \<equiv> let n = (of_char c :: nat) in
     if n < 128 then [of_nat n] else [of_nat (192 + n div 64), of_nat (128 + n mod 64)]\<close>

text\<open>\<^verbatim>\<open>PartialOrd::partial_cmp\<close> on integers: \<^verbatim>\<open>Some\<close> of the comparison.\<close>
definition partial_cmp_word :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s, ordering option, 'abort, 'i, 'o) function_body\<close> where
  \<open>partial_cmp_word a b \<equiv> FunctionBody (literal (Some (ord_cmp a b)))\<close>

section\<open>Hash maps\<close>

text\<open>A \<^verbatim>\<open>HashMap<K, V>\<close> whose iteration order is never observed is the list of its entries,
  with distinct keys; keys are compared by HOL's equality (the frontend uses these models only for
  keys whose \<^verbatim>\<open>PartialEq\<close> is structural).\<close>

definition hm_lookup :: \<open>('k \<times> 'v \<times> tnil) list \<Rightarrow> 'k \<Rightarrow> 'v option\<close> where
  \<open>hm_lookup m k \<equiv> map_option (\<lambda>e. fst (snd e)) (List.find (\<lambda>e. fst e = k) m)\<close>

definition hm_index :: \<open>('k \<times> 'v \<times> tnil) list \<Rightarrow> 'k \<Rightarrow> nat\<close> where
  \<open>hm_index m k \<equiv> length (takeWhile (\<lambda>e. fst e \<noteq> k) m)\<close>

definition hashmap_new :: \<open>('s, ('k \<times> 'v \<times> tnil) list, 'abort, 'i, 'o) function_body\<close> where
  \<open>hashmap_new \<equiv> FunctionBody (literal [])\<close>

definition hashmap_len :: \<open>('k \<times> 'v \<times> tnil) list \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>hashmap_len m \<equiv> FunctionBody (literal (of_nat (length m)))\<close>

definition hashmap_is_empty :: \<open>('k \<times> 'v \<times> tnil) list \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>hashmap_is_empty m \<equiv> FunctionBody (literal (m = []))\<close>

definition hashmap_contains_key :: \<open>('k \<times> 'v \<times> tnil) list \<Rightarrow> 'k \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>hashmap_contains_key m k \<equiv> FunctionBody (literal (hm_lookup m k \<noteq> None))\<close>

definition hashmap_get :: \<open>('k \<times> 'v \<times> tnil) list \<Rightarrow> 'k \<Rightarrow> ('s, 'v option, 'abort, 'i, 'o) function_body\<close> where
  \<open>hashmap_get m k \<equiv> FunctionBody (literal (hm_lookup m k))\<close>

text\<open>\<^verbatim>\<open>Range<T>\<close> (\<^verbatim>\<open>a..b\<close>) of an unsigned integer as an iterator: the start while it is
  below the end, each time increased.\<close>
definition range_next :: \<open>('l::len word range, 's, 'l word, 'abort, 'i, 'o) iter_step\<close> where
  \<open>range_next r \<equiv> FunctionBody (literal (if start r < end r
     then (Some (start r), make_range (start r + 1) (end r) (end_inclusive r), TNil) else (None, r, TNil)))\<close>

context reference
begin

adhoc_overloading store_update_const \<rightleftharpoons> update_fun

text\<open>\<^verbatim>\<open>Vec::push(&mut self, x)\<close>: appends \<open>x\<close>.\<close>
definition vec_push :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_push ptr x \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     ptr = \<llangle>ls @ [x]\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Vec::pop(&mut self)\<close>: removes the last element and returns it; \<^verbatim>\<open>None\<close> if empty.\<close>
definition vec_pop :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow>
      ('s, 'v option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_pop ptr \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>ls = []\<rrangle> {
        return None;
     };
     ptr = \<llangle>butlast ls\<rrangle>;
     \<llangle>Some (last ls)\<rrangle>
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open><[T]>::swap(&mut self, a, b)\<close>: exchanges the \<open>a\<close>-th and \<open>b\<close>-th elements; panics if
  either is out of bounds.\<close>
definition slice_swap :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_swap ptr a b \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>unat a < length ls \<and> unat b < length ls\<rrangle> {
        ptr = \<llangle>ls[unat a := ls ! unat b, unat b := ls ! unat a]\<rrangle>;
        ()
     } else {
        panic!("index out of bounds")
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Iterator::next(&mut self)\<close> of an iterator whose step function is \<open>nv\<close> (see
  @{typ \<open>('r, 's, 'v, 'abort, 'i, 'o) iter_step\<close>}).\<close>
definition iter_ref_next :: \<open>('r, 's, 'v, 'abort, 'i prompt, 'o prompt_output) iter_step \<Rightarrow>
    ('a, 'b, 'r) Global_Store.ref \<Rightarrow> ('s, 'v option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>iter_ref_next nv ptr \<equiv> FunctionBody \<lbrakk>
     let st = *ptr;
     let r = nv(st);
     ptr = r.1;
     r.0
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Vec::truncate(&mut self, len)\<close>: keeps the first \<open>len\<close> elements.\<close>
definition vec_truncate :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_truncate ptr n \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     ptr = \<llangle>take (unat n) ls\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Vec::clear(&mut self)\<close>.\<close>
definition vec_clear :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_clear ptr \<equiv> FunctionBody \<lbrakk>
     ptr = \<llangle>[]\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Vec::resize(&mut self, len, value)\<close>: truncates, or appends copies of \<open>value\<close>.\<close>
definition vec_resize :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow> 'v \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_resize ptr n x \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     ptr = \<llangle>take (unat n) ls @ replicate (unat n - length ls) x\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Vec::extend_from_slice(&mut self, other)\<close>.\<close>
definition vec_extend_from_slice :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 'v list \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_extend_from_slice ptr xs \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     ptr = \<llangle>ls @ xs\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open><[T]>::copy_from_slice(&mut self, src)\<close>: panics if the lengths differ.\<close>
definition slice_copy_from_slice :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 'v list \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_copy_from_slice ptr src \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>length src = length ls\<rrangle> {
        ptr = \<llangle>src\<rrangle>;
        ()
     } else {
        panic!("source slice length does not match destination slice length")
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open><[T]>::fill(&mut self, value)\<close>.\<close>
definition slice_fill :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_fill ptr x \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     ptr = \<llangle>replicate (length ls) x\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open><[T]>::reverse(&mut self)\<close>.\<close>
definition slice_reverse :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_reverse ptr \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     ptr = \<llangle>rev ls\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open><[T]>::copy_within(&mut self, src, dest)\<close> with a range \<open>src\<close>: copies the elements of
  \<open>src\<close> to the position \<open>dest\<close> (they may overlap); panics if either is out of bounds.\<close>
definition slice_copy_within :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word range \<Rightarrow> 64 word \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_copy_within ptr r d \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     match \<llangle>copy_within_opt ls (unat (start r)) (if end_inclusive r then unat (end r) + 1 else unat (end r)) (unat d)\<rrangle> {
       Some(ys) \<Rightarrow> {
         ptr = ys;
         ()
       },
       None \<Rightarrow> panic!("range out of bounds")
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Iterator::any(&mut self, f)\<close> of an iterator with step function \<open>nv\<close>.\<close>
definition iter_ref_any :: \<open>nat \<Rightarrow> ('r, 's, 'v, 'abort, 'i prompt, 'o prompt_output) iter_step \<Rightarrow>
    ('v \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body) \<Rightarrow>
    ('a, 'b, 'r) Global_Store.ref \<Rightarrow> ('s, bool, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>iter_ref_any fuel nv f ptr \<equiv> FunctionBody \<lbrakk>
     let st = *ptr;
     let g = \<llangle>iter_any_st fuel nv f\<rrangle>;
     let r = g(st);
     ptr = r.1;
     r.0
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open><[T]>::sort\<close>, \<^verbatim>\<open>sort_by\<close> with the comparison \<open>c\<close> (the frontend passes the \<^verbatim>\<open>Ord\<close> of
  the element type).\<close>
definition slice_sort_by :: \<open>('v \<Rightarrow> 'v \<Rightarrow> ordering) \<Rightarrow> ('a, 'b, 'v list) Global_Store.ref \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_sort_by c ptr \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     ptr = \<llangle>sort_by c ls\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Vec::dedup\<close> (structural equality).\<close>
definition vec_dedup :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_dedup ptr \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     ptr = \<llangle>dedup_list ls\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Vec::swap_remove(&mut self, i)\<close>: the \<open>i\<close>-th element, replaced by the last one; panics if
  \<open>i\<close> is out of bounds.\<close>
definition vec_swap_remove :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, 'v, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>vec_swap_remove ptr i \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>unat i < length ls\<rrangle> {
        ptr = \<llangle>butlast (ls[unat i := last ls])\<rrangle>;
        \<llangle>ls ! unat i\<rrangle>
     } else {
        panic!("swap_remove index out of bounds")
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>char::encode_utf8(self, &mut [u8])\<close> followed by \<^verbatim>\<open>as_bytes\<close>: writes the encoding to
  the start of the buffer (panics if it is too short) and returns it.\<close>
definition char_encode_utf8_bytes :: \<open>char \<Rightarrow> ('a, 'b, 8 word list) Global_Store.ref \<Rightarrow>
      ('s, 8 word list, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>char_encode_utf8_bytes c ptr \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>length (char_utf8 c) \<le> length ls\<rrangle> {
        ptr = \<llangle>char_utf8 c @ drop (length (char_utf8 c)) ls\<rrangle>;
        \<llangle>char_utf8 c\<rrangle>
     } else {
        panic!("encode_utf8: buffer too small")
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>HashMap::insert\<close>: replaces the value of an existing key (keeping the key), or adds the
  entry; the old value.\<close>
definition hashmap_insert :: \<open>('a, 'b, ('k \<times> 'v \<times> tnil) list) Global_Store.ref \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow>
      ('s, 'v option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>hashmap_insert ptr k v \<equiv> FunctionBody \<lbrakk>
     let m = *ptr;
     match \<llangle>hm_lookup m k\<rrangle> {
       Some(old) \<Rightarrow> {
         ptr = \<llangle>m[hm_index m k := (k, v, TNil)]\<rrangle>;
         Some(old)
       },
       None \<Rightarrow> {
         ptr = \<llangle>m @ [(k, v, TNil)]\<rrangle>;
         None
       }
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>HashMap::remove\<close>: the value of the key, removed.\<close>
definition hashmap_remove :: \<open>('a, 'b, ('k \<times> 'v \<times> tnil) list) Global_Store.ref \<Rightarrow> 'k \<Rightarrow>
      ('s, 'v option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>hashmap_remove ptr k \<equiv> FunctionBody \<lbrakk>
     let m = *ptr;
     ptr = \<llangle>List.filter (\<lambda>e. fst e \<noteq> k) m\<rrangle>;
     \<llangle>hm_lookup m k\<rrangle>
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>HashMap::get_mut\<close>: a reference to the value of the key, focused into the map.\<close>
definition hashmap_get_mut :: \<open>('a, 'b, ('k \<times> 'v \<times> tnil) list) Global_Store.ref \<Rightarrow> 'k \<Rightarrow>
      ('s, ('a, 'b, 'v) Global_Store.ref option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>hashmap_get_mut ptr k \<equiv> FunctionBody \<lbrakk>
     let m = *ptr;
     if \<llangle>hm_lookup m k \<noteq> None\<rrangle> {
       \<llangle>Some (focus_reference_via_lens (snd\<^sub>L \<circ>\<^sub>L fst\<^sub>L) (focus_nth (hm_index m k) ptr))\<rrangle>
     } else {
       None
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>HashMap::entry(k)\<close> followed by \<^verbatim>\<open>Entry::or_insert(v)\<close>: the entry \<^verbatim>\<open>(map, key)\<close>;
  \<^verbatim>\<open>or_insert\<close> adds \<open>(k, v)\<close> if the key is absent and returns a reference to the key's value.\<close>
definition hashmap_entry :: \<open>('a, 'b, ('k \<times> 'v \<times> tnil) list) Global_Store.ref \<Rightarrow> 'k \<Rightarrow>
      ('s, ('a, 'b, ('k \<times> 'v \<times> tnil) list) Global_Store.ref \<times> 'k \<times> tnil, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>hashmap_entry ptr k \<equiv> FunctionBody (literal (ptr, k, TNil))\<close>

definition hashmap_entry_or_insert :: \<open>('a, 'b, ('k \<times> 'v \<times> tnil) list) Global_Store.ref \<times> 'k \<times> tnil \<Rightarrow> 'v \<Rightarrow>
      ('s, ('a, 'b, 'v) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>hashmap_entry_or_insert e v \<equiv> FunctionBody \<lbrakk>
     let ptr = e.0;
     let k = e.1;
     let m = *ptr;
     if \<llangle>hm_lookup m k = None\<rrangle> {
       ptr = \<llangle>m @ [(k, v, TNil)]\<rrangle>;
     };
     let m2 = *ptr;
     \<llangle>focus_reference_via_lens (snd\<^sub>L \<circ>\<^sub>L fst\<^sub>L) (focus_nth (hm_index m2 k) ptr)\<rrangle>
  \<rbrakk>\<close>

no_adhoc_overloading store_update_const \<rightleftharpoons> update_fun

end

section\<open>Type variables of a definition's body only\<close>

text\<open>
  A type variable that occurs in the right-hand side of a definition \<open>c \<equiv> t\<close> but not in the
  type of \<open>c\<close> is not constrained by anything: the program never observes a value of that type
  (for instance the element type of an empty list that is only measured, or the value type of a
  \<^verbatim>\<open>return\<close> ending a loop body). Isabelle would make it an extra \<^typ>\<open>'a itself\<close>
  parameter of \<open>c\<close>, so that no use of \<open>c\<close> at its stated type type-checks. With the option
  \<open>urust_ground_body_types\<close> (set by the theories the frontend generates) such schematic type
  variables are instantiated with \<^typ>\<open>unit\<close> after type inference.
\<close>

ML\<open>
val urust_ground_body_types = Attrib.setup_config_bool \<^binding>\<open>urust_ground_body_types\<close> (K false);

fun urust_ground_body_type_vars ctxt ts =
  if not (Config.get ctxt urust_ground_body_types) then ts
  else
    let
      (*the type variables of the context's fixed variables, e.g. of a locale's parameters*)
      val context_tfrees =
        Vartab.fold (fn (_, T) => Term.add_tfreesT T) (#1 (Variable.constraints_of ctxt)) []
      fun ground (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ lhs $ rhs) t =
            let
              val stated = fastype_of lhs
              val tvars = subtract (op =) (Term.add_tvarsT stated []) (Term.add_tvars rhs [])
              val tfrees = subtract (op =) (Term.add_tfreesT stated context_tfrees) (Term.add_tfrees rhs [])
              val unit_for = (fn v => (v, \<^typ>\<open>unit\<close>))
            in
              t |> Term_Subst.instantiate (TVars.make (map unit_for tvars), Vars.empty)
                |> Term_Subst.instantiate_frees (TFrees.make (map unit_for tfrees), Frees.empty)
            end
        | ground _ t = t
    in map (fn t => ground t t) ts end;

val _ = Context.>> (Syntax_Phases.term_check 100 "urust_ground_body_types" urust_ground_body_type_vars);
\<close>

(*<*)
end
(*>*)
