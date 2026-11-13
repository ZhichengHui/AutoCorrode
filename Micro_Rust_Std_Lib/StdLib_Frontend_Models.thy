(*<*)
theory StdLib_Frontend_Models
  imports Crush.Crush StdLib_References StdLib_Ordering StdLib_Option StdLib_Result StdLib_Utf8 Misc.Result
    "HOL-Library.Sublist" "Word_Lib.Word_Lib_Sumo"
    \<comment>\<open>\<^verbatim>\<open>enum\<close>, for the enums the frontend declares with it\<close>
    "Enum_Theory.Enum_Theory"
  keywords "urust_const_data" :: thy_defn
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

section\<open>Strings and characters\<close>

text\<open>A \<^verbatim>\<open>str\<close> or \<^verbatim>\<open>String\<close> is the list of its UTF-8 bytes, a \<^verbatim>\<open>char\<close> its code point
  (see \<^verbatim>\<open>StdLib_Utf8\<close>). The models of methods that return new strings or iterators compute
  them at once; \<^verbatim>\<open>Lines\<close>, \<^verbatim>\<open>SplitWhitespace\<close>, \<^verbatim>\<open>Chars\<close>, \<^verbatim>\<open>CharIndices\<close> and
  \<^verbatim>\<open>Bytes\<close> are the lists of the remaining items.\<close>

definition strip_cr :: \<open>8 word list \<Rightarrow> 8 word list\<close> where
  \<open>strip_cr l \<equiv> if l \<noteq> [] \<and> last l = 0x0D then butlast l else l\<close>

text\<open>\<^verbatim>\<open>str::lines\<close>: \<^verbatim>\<open>split_inclusive('\n')\<close>, each piece without its \<^verbatim>\<open>\n\<close> and then
  without a \<^verbatim>\<open>\r\<close> before it (neither byte occurs inside a multi-byte sequence).\<close>
fun lines_aux :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list list\<close> where
  \<open>lines_aux cur [] = (if cur = [] then [] else [cur])\<close>
| \<open>lines_aux cur (c # cs) = (if c = 0x0A then strip_cr cur # lines_aux [] cs else lines_aux (cur @ [c]) cs)\<close>

definition str_lines :: \<open>8 word list \<Rightarrow> ('s, 8 word list list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_lines s \<equiv> FunctionBody (literal (lines_aux [] s))\<close>

fun words_aux :: \<open>32 word list \<Rightarrow> 32 word list \<Rightarrow> 32 word list list\<close> where
  \<open>words_aux cur [] = (if cur = [] then [] else [cur])\<close>
| \<open>words_aux cur (c # cs) = (if char_is_whitespace c then (if cur = [] then words_aux [] cs else cur # words_aux [] cs)
     else words_aux (cur @ [c]) cs)\<close>

text\<open>\<^verbatim>\<open>str::split_whitespace\<close>: the maximal non-empty runs of characters that are not
  \<^verbatim>\<open>char::is_whitespace\<close>.\<close>
definition str_split_whitespace :: \<open>8 word list \<Rightarrow> ('s, 8 word list list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_split_whitespace s \<equiv> FunctionBody (literal (List.map utf8_encode (words_aux [] (utf8_decode s))))\<close>

text\<open>\<^verbatim>\<open>str::trim\<close>, \<^verbatim>\<open>trim_start\<close>, \<^verbatim>\<open>trim_end\<close>: without the leading and/or trailing
  whitespace characters.\<close>
definition str_trim_start :: \<open>8 word list \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_trim_start s \<equiv> FunctionBody (literal (utf8_encode (dropWhile char_is_whitespace (utf8_decode s))))\<close>
definition str_trim_end :: \<open>8 word list \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_trim_end s \<equiv> FunctionBody (literal (utf8_encode (rev (dropWhile char_is_whitespace (rev (utf8_decode s))))))\<close>
definition str_trim :: \<open>8 word list \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_trim s \<equiv> FunctionBody (literal (utf8_encode
     (rev (dropWhile char_is_whitespace (rev (dropWhile char_is_whitespace (utf8_decode s)))))))\<close>

text\<open>\<^verbatim>\<open>str::starts_with\<close>, \<^verbatim>\<open>ends_with\<close>, \<^verbatim>\<open>strip_prefix\<close>, \<^verbatim>\<open>strip_suffix\<close>,
  \<^verbatim>\<open>contains\<close>, \<^verbatim>\<open>find\<close> with a \<^verbatim>\<open>char\<close> or a \<^verbatim>\<open>&str\<close> pattern: on the bytes (a
  character is its encoding; a match of valid UTF-8 in valid UTF-8 starts at a character
  boundary).\<close>
definition str_starts_with_char :: \<open>8 word list \<Rightarrow> 32 word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_starts_with_char s c \<equiv> FunctionBody (literal (prefix (char_utf8 c) s))\<close>
definition str_starts_with_str :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_starts_with_str s p \<equiv> FunctionBody (literal (prefix p s))\<close>
definition str_ends_with_char :: \<open>8 word list \<Rightarrow> 32 word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_ends_with_char s c \<equiv> FunctionBody (literal (suffix (char_utf8 c) s))\<close>
definition str_ends_with_str :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_ends_with_str s p \<equiv> FunctionBody (literal (suffix p s))\<close>
definition str_strip_prefix_char :: \<open>8 word list \<Rightarrow> 32 word \<Rightarrow> ('s, 8 word list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_strip_prefix_char s c \<equiv> FunctionBody (literal
     (if prefix (char_utf8 c) s then Some (drop (length (char_utf8 c)) s) else None))\<close>
definition str_strip_prefix_str :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> ('s, 8 word list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_strip_prefix_str s p \<equiv> FunctionBody (literal (if prefix p s then Some (drop (length p) s) else None))\<close>
definition str_strip_suffix_char :: \<open>8 word list \<Rightarrow> 32 word \<Rightarrow> ('s, 8 word list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_strip_suffix_char s c \<equiv> FunctionBody (literal
     (if suffix (char_utf8 c) s then Some (take (length s - length (char_utf8 c)) s) else None))\<close>
definition str_strip_suffix_str :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> ('s, 8 word list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_strip_suffix_str s p \<equiv> FunctionBody (literal (if suffix p s then Some (take (length s - length p) s) else None))\<close>

text\<open>The first position from \<open>i\<close> on where \<open>p\<close> occurs in \<open>s\<close>.\<close>
fun bytes_find :: \<open>nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> nat option\<close> where
  \<open>bytes_find i p [] = (if p = [] then Some i else None)\<close>
| \<open>bytes_find i p (b # bs) = (if prefix p (b # bs) then Some i else bytes_find (i + 1) p bs)\<close>

definition str_find_str :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> ('s, 64 word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_find_str s p \<equiv> FunctionBody (literal (map_option of_nat (bytes_find 0 p s)))\<close>
definition str_find_char :: \<open>8 word list \<Rightarrow> 32 word \<Rightarrow> ('s, 64 word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_find_char s c \<equiv> FunctionBody (literal (map_option of_nat (bytes_find 0 (char_utf8 c) s)))\<close>
definition str_contains_str :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_contains_str s p \<equiv> FunctionBody (literal (bytes_find 0 p s \<noteq> None))\<close>
definition str_contains_char :: \<open>8 word list \<Rightarrow> 32 word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_contains_char s c \<equiv> FunctionBody (literal (bytes_find 0 (char_utf8 c) s \<noteq> None))\<close>

text\<open>\<^verbatim>\<open>str::as_bytes\<close>: the bytes themselves.\<close>
definition str_as_bytes :: \<open>8 word list \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_as_bytes s \<equiv> FunctionBody (literal s)\<close>

text\<open>\<^verbatim>\<open>str::chars\<close>, \<^verbatim>\<open>str::char_indices\<close> (each character with its byte offset).\<close>
definition str_chars :: \<open>8 word list \<Rightarrow> ('s, 32 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_chars s \<equiv> FunctionBody (literal (utf8_decode s))\<close>

fun char_indices_aux :: \<open>nat \<Rightarrow> 32 word list \<Rightarrow> (64 word \<times> 32 word \<times> tnil) list\<close> where
  \<open>char_indices_aux i [] = []\<close>
| \<open>char_indices_aux i (c # cs) = (of_nat i, c, TNil) # char_indices_aux (i + length (char_utf8 c)) cs\<close>

definition str_char_indices :: \<open>8 word list \<Rightarrow> ('s, (64 word \<times> 32 word \<times> tnil) list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_char_indices s \<equiv> FunctionBody (literal (char_indices_aux 0 (utf8_decode s)))\<close>

definition str_is_char_boundary_fn :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_is_char_boundary_fn s i \<equiv> FunctionBody (literal (str_is_char_boundary s (unat i)))\<close>

text\<open>\<^verbatim>\<open>is_ascii\<close>, \<^verbatim>\<open>eq_ignore_ascii_case\<close>, \<^verbatim>\<open>to_ascii_uppercase\<close>,
  \<^verbatim>\<open>to_ascii_lowercase\<close> on a string or a byte slice.\<close>
definition bytes_is_ascii :: \<open>8 word list \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>bytes_is_ascii s \<equiv> FunctionBody (literal (list_all (\<lambda>b. b < 0x80) s))\<close>
definition bytes_eq_ignore_ascii_case :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>bytes_eq_ignore_ascii_case a b \<equiv> FunctionBody (literal (List.map ascii_lower a = List.map ascii_lower b))\<close>
definition bytes_to_ascii_uppercase :: \<open>8 word list \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>bytes_to_ascii_uppercase s \<equiv> FunctionBody (literal (List.map ascii_upper s))\<close>
definition bytes_to_ascii_lowercase :: \<open>8 word list \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>bytes_to_ascii_lowercase s \<equiv> FunctionBody (literal (List.map ascii_lower s))\<close>

text\<open>\<^verbatim>\<open>str::repeat(n)\<close>: panics when the length exceeds \<^verbatim>\<open>isize::MAX\<close> (the capacity
  overflows).\<close>
definition str_repeat :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_repeat s n \<equiv> FunctionBody \<lbrakk>
     if \<llangle>length s * unat n \<ge> 2 ^ 63\<rrangle> { panic!("capacity overflow") };
     \<llangle>List.concat (List.replicate (unat n) s)\<rrangle>
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>String + &str\<close>.\<close>
definition string_add :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>string_add a b \<equiv> FunctionBody (literal (a @ b))\<close>

text\<open>\<^verbatim>\<open>Ord::cmp\<close> on strings: the lexicographic order of the bytes, which is the order of the
  characters.\<close>
definition str_ord :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> ordering\<close> where
  \<open>str_ord a b \<equiv> let r = bytes_cmp a b in if r < 0 then Less else if r = 0 then Equal else Greater\<close>
definition str_cmp :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> ('s, ordering, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_cmp a b \<equiv> FunctionBody (literal (str_ord a b))\<close>

subsection\<open>Substrings\<close>

text\<open>The bytes from \<open>a\<close> to \<open>b\<close>, if \<open>a \<le> b \<le> length s\<close> and both are character
  boundaries.\<close>
definition str_sub_opt :: \<open>8 word list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 8 word list option\<close> where
  \<open>str_sub_opt s a b \<equiv>
     if a \<le> b \<and> b \<le> length s \<and> str_is_char_boundary s a \<and> str_is_char_boundary s b
     then Some (take (b - a) (drop a s)) else None\<close>

text\<open>The substring of a range \<^verbatim>\<open>a..b\<close>, \<^verbatim>\<open>a..=b\<close> (a \<^typ>\<open>64 word range\<close>), \<^verbatim>\<open>..b\<close>,
  \<^verbatim>\<open>..=b\<close>, \<^verbatim>\<open>a..\<close> (by their only field).\<close>
definition str_range_opt :: \<open>8 word list \<Rightarrow> 64 word range \<Rightarrow> 8 word list option\<close> where
  \<open>str_range_opt s r \<equiv> str_sub_opt s (unat (start r)) (if end_inclusive r then unat (end r) + 1 else unat (end r))\<close>
definition str_to_opt :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> 8 word list option\<close> where
  \<open>str_to_opt s b \<equiv> str_sub_opt s 0 (unat b)\<close>
definition str_to_inclusive_opt :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> 8 word list option\<close> where
  \<open>str_to_inclusive_opt s b \<equiv> str_sub_opt s 0 (unat b + 1)\<close>
definition str_from_opt :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> 8 word list option\<close> where
  \<open>str_from_opt s a \<equiv> str_sub_opt s (unat a) (length s)\<close>

text\<open>\<^verbatim>\<open>str::get\<close> by a range.\<close>
definition str_get_range :: \<open>8 word list \<Rightarrow> 64 word range \<Rightarrow> ('s, 8 word list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_get_range s r \<equiv> FunctionBody (literal (str_range_opt s r))\<close>
definition str_get_to :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> ('s, 8 word list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_get_to s b \<equiv> FunctionBody (literal (str_to_opt s b))\<close>
definition str_get_to_inclusive :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> ('s, 8 word list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_get_to_inclusive s b \<equiv> FunctionBody (literal (str_to_inclusive_opt s b))\<close>
definition str_get_from :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> ('s, 8 word list option, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_get_from s a \<equiv> FunctionBody (literal (str_from_opt s a))\<close>

text\<open>\<^verbatim>\<open>s[r]\<close> on a \<^verbatim>\<open>str\<close>: panics where \<^verbatim>\<open>get\<close> gives \<^verbatim>\<open>None\<close>.\<close>
definition str_index_opt :: \<open>8 word list option \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_index_opt r \<equiv> FunctionBody \<lbrakk>
     match r {
       Some(x) \<Rightarrow> x,
       None \<Rightarrow> panic!("byte index out of bounds or not on a char boundary")
     }
  \<rbrakk>\<close>
definition str_index_range :: \<open>8 word list \<Rightarrow> 64 word range \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_index_range s r \<equiv> str_index_opt (str_range_opt s r)\<close>
definition str_index_to :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_index_to s b \<equiv> str_index_opt (str_to_opt s b)\<close>
definition str_index_to_inclusive :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_index_to_inclusive s b \<equiv> str_index_opt (str_to_inclusive_opt s b)\<close>
definition str_index_from :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_index_from s a \<equiv> str_index_opt (str_from_opt s a)\<close>

text\<open>\<^verbatim>\<open>str::split_at(mid)\<close>: panics if \<open>mid\<close> is not a character boundary.\<close>
definition str_split_at :: \<open>8 word list \<Rightarrow> 64 word \<Rightarrow> ('s, 8 word list \<times> 8 word list \<times> tnil, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_split_at s m \<equiv> FunctionBody \<lbrakk>
     if \<llangle>\<not> str_is_char_boundary s (unat m)\<rrangle> { panic!("failed to slice string") };
     \<llangle>(take (unat m) s, drop (unat m) s, TNil)\<rrangle>
  \<rbrakk>\<close>

subsection\<open>UTF-8 conversion\<close>

text\<open>\<^verbatim>\<open>alloc::string::FromUtf8Error\<close>: the bytes and the \<^verbatim>\<open>Utf8Error\<close>.\<close>
datatype from_utf8_error = FromUtf8Error (from_utf8_error_bytes: \<open>8 word list\<close>) (from_utf8_error_error: utf8_error)

definition utf8_result :: \<open>8 word list \<Rightarrow> (8 word list, utf8_error) result\<close> where
  \<open>utf8_result bs \<equiv> case utf8_check 0 bs of None \<Rightarrow> Ok bs | Some (i, l) \<Rightarrow> Err (Utf8Error (of_nat i) l)\<close>

text\<open>\<^verbatim>\<open>str::from_utf8\<close>, \<^verbatim>\<open>String::from_utf8\<close>: the bytes if they are valid UTF-8.\<close>
definition str_from_utf8 :: \<open>8 word list \<Rightarrow> ('s, (8 word list, utf8_error) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_from_utf8 bs \<equiv> FunctionBody (literal (utf8_result bs))\<close>
definition string_from_utf8 :: \<open>8 word list \<Rightarrow> ('s, (8 word list, from_utf8_error) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>string_from_utf8 bs \<equiv> FunctionBody (literal (case utf8_result bs of
     Ok s \<Rightarrow> Ok s | Err e \<Rightarrow> Err (FromUtf8Error bs e)))\<close>

text\<open>The accessors of \<^verbatim>\<open>Utf8Error\<close> and \<^verbatim>\<open>FromUtf8Error\<close>.\<close>
definition utf8_error_valid_up_to_fn :: \<open>utf8_error \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>utf8_error_valid_up_to_fn e \<equiv> FunctionBody (literal (utf8_error_valid_up_to e))\<close>
definition utf8_error_error_len_fn :: \<open>utf8_error \<Rightarrow> ('s, 64 word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>utf8_error_error_len_fn e \<equiv> FunctionBody (literal (map_option ucast (utf8_error_len e)))\<close>
definition from_utf8_error_utf8_error :: \<open>from_utf8_error \<Rightarrow> ('s, utf8_error, 'abort, 'i, 'o) function_body\<close> where
  \<open>from_utf8_error_utf8_error e \<equiv> FunctionBody (literal (from_utf8_error_error e))\<close>
definition from_utf8_error_into_bytes :: \<open>from_utf8_error \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>from_utf8_error_into_bytes e \<equiv> FunctionBody (literal (from_utf8_error_bytes e))\<close>

subsection\<open>Characters\<close>

text\<open>\<^verbatim>\<open>char::from_u32\<close>, \<^verbatim>\<open>char::TryFrom<u32>\<close> (as an \<^verbatim>\<open>Option\<close>).\<close>
definition char_from_u32 :: \<open>32 word \<Rightarrow> ('s, 32 word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>char_from_u32 n \<equiv> FunctionBody (literal (if is_scalar n then Some n else None))\<close>

text\<open>\<^verbatim>\<open>char::len_utf8\<close>.\<close>
definition char_len_utf8 :: \<open>32 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>char_len_utf8 c \<equiv> FunctionBody (literal (of_nat (length (char_utf8 c))))\<close>

text\<open>\<^verbatim>\<open>ToString::to_string\<close>, \<^verbatim>\<open>String::from\<close> of a \<^verbatim>\<open>char\<close>.\<close>
definition char_to_string :: \<open>32 word \<Rightarrow> ('s, 8 word list, 'abort, 'i, 'o) function_body\<close> where
  \<open>char_to_string c \<equiv> FunctionBody (literal (char_utf8 c))\<close>

text\<open>\<^verbatim>\<open>char::to_digit(radix)\<close>, \<^verbatim>\<open>char::from_digit(num, radix)\<close>.\<close>
definition char_to_digit :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, 32 word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>char_to_digit c radix \<equiv> FunctionBody \<lbrakk>
     if \<llangle>radix < 2 \<or> 36 < radix\<rrangle> {
       panic!("to_digit: invalid radix -- radix must be in the range 2 to 36 inclusive")
     };
     \<llangle>if char_digit_value c radix < radix then Some (char_digit_value c radix) else None\<rrangle>
  \<rbrakk>\<close>
definition char_from_digit :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> ('s, 32 word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>char_from_digit n radix \<equiv> FunctionBody \<lbrakk>
     if \<llangle>36 < radix\<rrangle> { panic!("from_digit: radix is too high (maximum 36)") };
     \<llangle>if n < radix then Some (if n < 10 then 48 + n else 87 + n) else None\<rrangle>
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>char::is_whitespace\<close>, \<^verbatim>\<open>char::is_control\<close>.\<close>
definition char_is_whitespace_fn :: \<open>32 word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>char_is_whitespace_fn c \<equiv> FunctionBody (literal (char_is_whitespace c))\<close>
definition char_is_control_fn :: \<open>32 word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>char_is_control_fn c \<equiv> FunctionBody (literal (char_is_control c))\<close>

text\<open>The ASCII methods of \<^verbatim>\<open>u8\<close> and \<^verbatim>\<open>char\<close>: \<^verbatim>\<open>is_ascii_digit\<close> and the other
  classes (the class \<open>p\<close> on the code), \<^verbatim>\<open>to_ascii_uppercase\<close>, \<^verbatim>\<open>to_ascii_lowercase\<close>,
  \<^verbatim>\<open>eq_ignore_ascii_case\<close>.\<close>
definition ascii_test :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> 'l::len word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>ascii_test p c \<equiv> FunctionBody (literal (unat c < 128 \<and> p (unat c)))\<close>
definition ascii_to_uppercase :: \<open>'l::len word \<Rightarrow> ('s, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>ascii_to_uppercase c \<equiv> FunctionBody (literal (ascii_upper c))\<close>
definition ascii_to_lowercase :: \<open>'l::len word \<Rightarrow> ('s, 'l word, 'abort, 'i, 'o) function_body\<close> where
  \<open>ascii_to_lowercase c \<equiv> FunctionBody (literal (ascii_lower c))\<close>
definition ascii_eq_ignore_case :: \<open>'l::len word \<Rightarrow> 'l word \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>ascii_eq_ignore_case a b \<equiv> FunctionBody (literal (ascii_lower a = ascii_lower b))\<close>

subsection\<open>Parsing integers\<close>

text\<open>\<^verbatim>\<open>core::num::IntErrorKind\<close>; a \<^verbatim>\<open>ParseIntError\<close> is its only field.\<close>
datatype int_error_kind = IntErrorKind_Empty | IntErrorKind_InvalidDigit | IntErrorKind_PosOverflow
  | IntErrorKind_NegOverflow | IntErrorKind_Zero

text\<open>The digits in base \<open>r\<close> after the sign, as \<^verbatim>\<open>from_ascii_bytes_radix\<close>: a byte that is not a
  digit (\<^verbatim>\<open>char::to_digit\<close>) is an error before the overflow of the value accumulated so far.\<close>
fun parse_digits :: \<open>32 word \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 8 word list \<Rightarrow> (int, int_error_kind) result\<close> where
  \<open>parse_digits r neg lo hi a [] = Ok a\<close>
| \<open>parse_digits r neg lo hi a (c # cs) =
     (let v = char_digit_value (ucast c) r in
      if \<not> v < r then Err IntErrorKind_InvalidDigit
      else let d = int (unat v); a' = (if neg then a * int (unat r) - d else a * int (unat r) + d) in
        if neg \<and> a' < lo then Err IntErrorKind_NegOverflow
        else if \<not> neg \<and> hi < a' then Err IntErrorKind_PosOverflow
        else parse_digits r neg lo hi a' cs)\<close>

definition parse_int :: \<open>32 word \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 8 word list \<Rightarrow> (int, int_error_kind) result\<close> where
  \<open>parse_int r sg lo hi s \<equiv> (case s of
      [] \<Rightarrow> Err IntErrorKind_Empty
    | c # rest \<Rightarrow> if (c = 43 \<or> c = 45) \<and> rest = [] then Err IntErrorKind_InvalidDigit
        else if c = 43 then parse_digits r False lo hi 0 rest
        else if c = 45 \<and> sg then parse_digits r True lo hi 0 rest
        else parse_digits r False lo hi 0 s)\<close>

definition parse_word_result :: \<open>32 word \<Rightarrow> 8 word list \<Rightarrow> ('l::len word, int_error_kind) result\<close> where
  \<open>parse_word_result r s \<equiv> case parse_int r False 0 (2 ^ LENGTH('l) - 1) s of
     Ok n \<Rightarrow> Ok (word_of_int n) | Err e \<Rightarrow> Err e\<close>
definition parse_sword_result :: \<open>32 word \<Rightarrow> 8 word list \<Rightarrow> ('l::len sword, int_error_kind) result\<close> where
  \<open>parse_sword_result r s \<equiv> case parse_int r True (- (2 ^ (LENGTH('l) - 1))) (2 ^ (LENGTH('l) - 1) - 1) s of
     Ok n \<Rightarrow> Ok (word_of_int n) | Err e \<Rightarrow> Err e\<close>

text\<open>\<^verbatim>\<open>str::parse\<close> into an unsigned and into a signed integer type.\<close>
definition str_parse_word :: \<open>8 word list \<Rightarrow> ('s, ('l::len word, int_error_kind) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_parse_word s \<equiv> FunctionBody (literal (parse_word_result 10 s))\<close>
definition str_parse_sword :: \<open>8 word list \<Rightarrow> ('s, ('l::len sword, int_error_kind) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>str_parse_sword s \<equiv> FunctionBody (literal (parse_sword_result 10 s))\<close>

text\<open>\<^verbatim>\<open>from_str_radix(src, radix)\<close> of the integer types: panics if the radix is not from 2
  to 36.\<close>
definition from_str_radix_word :: \<open>8 word list \<Rightarrow> 32 word \<Rightarrow> ('s, ('l::len word, int_error_kind) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>from_str_radix_word s r \<equiv> FunctionBody \<lbrakk>
     if \<llangle>r < 2 \<or> 36 < r\<rrangle> { panic!("from_ascii_bytes_radix: radix must lie in the range `[2, 36]`") };
     \<llangle>parse_word_result r s\<rrangle>
  \<rbrakk>\<close>
definition from_str_radix_sword :: \<open>8 word list \<Rightarrow> 32 word \<Rightarrow> ('s, ('l::len sword, int_error_kind) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>from_str_radix_sword s r \<equiv> FunctionBody \<lbrakk>
     if \<llangle>r < 2 \<or> 36 < r\<rrangle> { panic!("from_ascii_bytes_radix: radix must lie in the range `[2, 36]`") };
     \<llangle>parse_sword_result r s\<rrangle>
  \<rbrakk>\<close>

text\<open>The message argument of \<^verbatim>\<open>Option::expect\<close>, \<^verbatim>\<open>Result::expect\<close> (a Rust string) as the
  panic message.\<close>
definition option_expect_str :: \<open>'v option \<Rightarrow> 8 word list \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>option_expect_str opt m \<equiv> option_expect opt (str_message m)\<close>
definition result_expect_str :: \<open>('v, 'e) result \<Rightarrow> 8 word list \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>result_expect_str r m \<equiv> result_expect r (str_message m)\<close>

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

subsection\<open>Subslices\<close>

text\<open>The part of a list after its first \<open>a\<close> elements and before its last \<open>k\<close> ones.\<close>
definition sublist_view :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v list \<Rightarrow> 'v list option\<close> where
  \<open>sublist_view a k xs \<equiv>
     if a + k \<le> length xs then Some (List.take (length xs - a - k) (List.drop a xs)) else None\<close>

definition sublist_modify :: \<open>nat \<Rightarrow> nat \<Rightarrow> ('v list \<Rightarrow> 'v list) \<Rightarrow> 'v list \<Rightarrow> 'v list\<close> where
  \<open>sublist_modify a k f xs \<equiv>
     if a + k \<le> length xs then
       List.take a xs @ f (List.take (length xs - a - k) (List.drop a xs)) @ List.drop (length xs - k) xs
     else xs\<close>

lemma sublist_split:
  assumes \<open>a + k \<le> length xs\<close>
  shows \<open>List.take a xs @ List.take (length xs - a - k) (List.drop a xs) @ List.drop (length xs - k) xs = xs\<close>
proof -
  have \<open>List.drop (length xs - k) xs = List.drop (length xs - a - k) (List.drop a xs)\<close>
    using assms by (simp add: add.commute)
  then show ?thesis
    by (simp only: append_take_drop_id)
qed

lemma sublist_modify_view:
  shows \<open>sublist_view a k (sublist_modify a k f xs) = map_option f (sublist_view a k xs)\<close>
  by (auto simp add: sublist_view_def sublist_modify_def)

lemma sublist_modify_id:
  assumes \<open>map_option f (sublist_view a k xs) = sublist_view a k xs\<close>
  shows \<open>sublist_modify a k f xs = xs\<close>
  using assms sublist_split[of a k xs] by (auto simp add: sublist_view_def sublist_modify_def)

lemma sublist_modify_comp:
  shows \<open>sublist_modify a k f (sublist_modify a k g xs) = sublist_modify a k (\<lambda>x. f (g x)) xs\<close>
  by (auto simp add: sublist_modify_def)

text\<open>The focus of a mutable borrow of a subslice: on the elements between the first \<open>a\<close> and
  the last \<open>k\<close>. It is valid, unlike a focus on the fixed positions \<open>a..b\<close> (an update of another
  length would break it, see \<^verbatim>\<open>StdLib_Slice\<close>); the two agree on the lists of the same
  length, and a slice keeps its length.\<close>
lift_definition sublist_focus :: \<open>nat \<Rightarrow> nat \<Rightarrow> ('v list, 'v list) focus\<close> is
  \<open>\<lambda>a k. make_focus_raw_via_view_modify (sublist_view a k) (sublist_modify a k)\<close>
  by (intro is_valid_focus_via_modifyI)
     (auto simp add: sublist_modify_view sublist_modify_id sublist_modify_comp)

lemma sublist_focus_components [focus_components]:
  shows \<open>focus_view (sublist_focus a k) = sublist_view a k\<close>
    and \<open>focus_update (sublist_focus a k) y xs = sublist_modify a k (\<lambda>_. y) xs\<close>
    and \<open>focus_modify (sublist_focus a k) f xs = sublist_modify a k f xs\<close>
  apply (transfer; clarsimp simp add: make_focus_raw_via_view_modify_def)
  apply (transfer; clarsimp simp add: make_focus_raw_via_view_modify_def)
  apply (transfer; clarsimp simp add: make_focus_raw_via_view_modify_components sublist_modify_view
    sublist_modify_id sublist_modify_comp is_valid_view_modify_def)
  done

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

section\<open>Comparisons\<close>

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

text\<open>\<^verbatim>\<open>Range<T>\<close> (\<^verbatim>\<open>a..b\<close>) and \<^verbatim>\<open>RangeInclusive<T>\<close> (\<^verbatim>\<open>a..=b\<close>) of an unsigned
  integer as an iterator, from the front and from the back. An exhausted \<^verbatim>\<open>a..=b\<close> (Rust's flag
  \<open>exhausted\<close>) is the empty \<^verbatim>\<open>b+1..b+1\<close>, the range Rust indexes a slice with
  (\<^verbatim>\<open>b..b\<close> for the largest \<open>b\<close>: as \<^verbatim>\<open>b+1\<close> overflows, a slice is shorter than it).\<close>
definition range_exhausted :: \<open>'l::len word \<Rightarrow> 'l word range\<close> where
  \<open>range_exhausted b \<equiv> if b = - 1 then make_range b b False else make_range (b + 1) (b + 1) False\<close>

definition range_next :: \<open>('l::len word range, 's, 'l word, 'abort, 'i, 'o) iter_step\<close> where
  \<open>range_next r \<equiv> FunctionBody (literal (
     if end_inclusive r then
       (if start r \<le> end r then
          (Some (start r), (if start r = end r then range_exhausted (end r)
                            else make_range (start r + 1) (end r) True), TNil)
        else (None, r, TNil))
     else if start r < end r then (Some (start r), make_range (start r + 1) (end r) False, TNil)
     else (None, r, TNil)))\<close>

definition range_next_back :: \<open>('l::len word range, 's, 'l word, 'abort, 'i, 'o) iter_step\<close> where
  \<open>range_next_back r \<equiv> FunctionBody (literal (
     if end_inclusive r then
       (if start r \<le> end r then
          (Some (end r), (if start r = end r then range_exhausted (end r)
                          else make_range (start r) (end r - 1) True), TNil)
        else (None, r, TNil))
     else if start r < end r then (Some (end r - 1), make_range (start r) (end r - 1) False, TNil)
     else (None, r, TNil)))\<close>

text\<open>\<^verbatim>\<open>Iterator::for_each\<close>: calls the function on every item, in order.\<close>
definition iter_for_each :: \<open>nat \<Rightarrow> ('r, 's, 'v, 'abort, 'i, 'o) iter_step \<Rightarrow> ('v \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body) \<Rightarrow>
    'r \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>iter_for_each fuel nv f st \<equiv> iter_fold fuel nv (\<lambda>u x. FunctionBody \<lbrakk> f(x) \<rbrakk>) st ()\<close>

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
definition char_encode_utf8_bytes :: \<open>32 word \<Rightarrow> ('a, 'b, 8 word list) Global_Store.ref \<Rightarrow>
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

text\<open>\<^verbatim>\<open>String::push(&mut self, c)\<close>: appends the encoding of \<open>c\<close>.\<close>
definition string_push :: \<open>('a, 'b, 8 word list) Global_Store.ref \<Rightarrow> 32 word \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>string_push ptr c \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     ptr = \<llangle>ls @ char_utf8 c\<rrangle>;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>String::pop(&mut self)\<close>: removes and returns the last character.\<close>
definition string_pop :: \<open>('a, 'b, 8 word list) Global_Store.ref \<Rightarrow>
      ('s, 32 word option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>string_pop ptr \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>ls = []\<rrangle> {
        return None;
     };
     let c = \<llangle>last (utf8_decode ls)\<rrangle>;
     ptr = \<llangle>take (length ls - length (char_utf8 c)) ls\<rrangle>;
     Some(c)
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>String::truncate(&mut self, new_len)\<close>: no effect if \<open>new_len\<close> is not below the
  length; panics if it is not a character boundary.\<close>
definition string_truncate :: \<open>('a, 'b, 8 word list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>string_truncate ptr n \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>unat n \<le> length ls \<and> \<not> str_is_char_boundary ls (unat n)\<rrangle> {
        panic!("assertion failed: self.is_char_boundary(new_len)")
     };
     ptr = \<llangle>take (unat n) ls\<rrangle>;
     ()
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

text\<open>\<^verbatim>\<open>mem::swap(x, y)\<close>.\<close>
definition mem_swap :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> ('a, 'b, 'v) Global_Store.ref \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>mem_swap x y \<equiv> FunctionBody \<lbrakk>
     let a = *x;
     let b = *y;
     x = b;
     y = a;
     ()
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>mem::replace(dest, v)\<close>: the old value.\<close>
definition mem_replace :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
      ('s, 'v, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>mem_replace x v \<equiv> FunctionBody \<lbrakk>
     let old = *x;
     x = v;
     old
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open><[T]>::get_mut(i)\<close>: a reference to the \<open>i\<close>-th element, \<^verbatim>\<open>None\<close> if out of bounds.\<close>
definition slice_get_mut :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, ('a, 'b, 'v) Global_Store.ref option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_get_mut ptr i \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>unat i < length ls\<rrangle> {
       \<llangle>Some (focus_nth (unat i) ptr)\<rrangle>
     } else {
       None
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open><[T]>::iter_mut()\<close> as a value: the references to the elements (the state of
  \<^verbatim>\<open>slice::IterMut\<close>).\<close>
definition slice_iter_mut_list :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow>
      ('s, ('a, 'b, 'v) Global_Store.ref list, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_iter_mut_list ptr \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     \<llangle>List.map (\<lambda>i. focus_nth i ptr) [0 ..< length ls]\<rrangle>
  \<rbrakk>\<close>

text\<open>The reference to the subslice \<open>[lo, hi)\<close> of the slice \<open>ptr\<close> refers to (focused on the
  elements between the \<open>lo\<close> before and the \<open>len - hi\<close> after it); a panic unless
  \<open>lo \<le> hi \<le> len\<close>.\<close>
definition slice_sub_mut :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      ('s, ('a, 'b, 'v list) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_sub_mut ptr lo hi \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     if \<llangle>lo \<le> hi \<and> hi \<le> length ls\<rrangle> {
       \<llangle>focus_focused (sublist_focus lo (length ls - hi)) ptr\<rrangle>
     } else {
       panic!("slice index out of range")
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>&mut s[r]\<close> for a range \<open>r\<close> (\<^verbatim>\<open>a..b\<close>, \<^verbatim>\<open>a..=b\<close>), \<^verbatim>\<open>a..\<close>, \<^verbatim>\<open>..b\<close> and
  \<^verbatim>\<open>..=b\<close> (the last three by their only bound).\<close>
definition slice_range_mut :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word range \<Rightarrow>
      ('s, ('a, 'b, 'v list) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_range_mut ptr r \<equiv> slice_sub_mut ptr (unat (start r)) (if end_inclusive r then unat (end r) + 1 else unat (end r))\<close>

definition slice_range_from_mut :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, ('a, 'b, 'v list) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_range_from_mut ptr lo \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     slice_sub_mut(ptr, \<llangle>unat lo\<rrangle>, \<llangle>length ls\<rrangle>)
  \<rbrakk>\<close>

definition slice_range_to_mut :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, ('a, 'b, 'v list) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_range_to_mut ptr hi \<equiv> slice_sub_mut ptr 0 (unat hi)\<close>

definition slice_range_to_inclusive_mut :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, ('a, 'b, 'v list) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_range_to_inclusive_mut ptr hi \<equiv> slice_sub_mut ptr 0 (unat hi + 1)\<close>

text\<open>\<^verbatim>\<open><[T]>::get_mut(r)\<close> for a range \<open>r\<close> (\<^verbatim>\<open>a..b\<close>, \<^verbatim>\<open>a..=b\<close>): the reference to the
  subslice, \<^verbatim>\<open>None\<close> if the range is decreasing or exceeds the slice.\<close>
definition slice_get_range_mut :: \<open>('a, 'b, 'v list) Global_Store.ref \<Rightarrow> 64 word range \<Rightarrow>
      ('s, ('a, 'b, 'v list) Global_Store.ref option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>slice_get_range_mut ptr r \<equiv> FunctionBody \<lbrakk>
     let ls = *ptr;
     let lo = \<llangle>unat (start r)\<rrangle>;
     let hi = \<llangle>if end_inclusive r then unat (end r) + 1 else unat (end r)\<rrangle>;
     if \<llangle>lo \<le> hi \<and> hi \<le> length ls\<rrangle> {
       \<llangle>Some (focus_focused (sublist_focus lo (length ls - hi)) ptr)\<rrangle>
     } else {
       None
     }
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

text\<open>A Rust constant with a large value (for instance a lookup table of 10^5 entries) is
  translated from the value computed by Rust's constant evaluation, with

  \<^verbatim>\<open>urust_const_data "c" :: \<open>T\<close> = \<open>data\<close>\<close>

  which defines \<open>c \<equiv> FunctionBody (literal v)\<close> of type \<open>T\<close>, a \<^typ>\<open>('s, 'v, 'abort, 'i, 'o) function_body\<close>.
  The value \<open>v :: 'v\<close> is given by \<open>data\<close>:
  \<^item> an integer, possibly negative, a numeral of the expected type;
  \<^item> \<open>name\<close> or \<open>name(d1, .., dn)\<close>, the constant \<open>name\<close> applied to the values \<open>d1\<close>, .., \<open>dn\<close>;
  \<^item> \<open>[d1, .., dn]\<close>, a list; \<open>()\<close>, the unit; \<open>(d1, .., dn)\<close> for \<open>n \<ge> 2\<close>, a tuple.
  The term is built in one pass over the data, from the expected type down: the inner syntax
  (parsing and type inference) takes time superlinear in the size of such a term, and does not
  finish for tables of this size. Only the small term \<open>FunctionBody (literal x)\<close> is checked. A list of
  more than 256 elements is a balanced tree of appends \<open>(l1 @ l2) @ (l3 @ l4)\<close> of lists of at most 256
  elements: the definition takes time superlinear in the depth of the term.\<close>

ML\<open>
structure Urust_Const_Data =
struct

datatype data = Int of int | App of string * data list | List of data list | Tuple of data list

fun parse s =
  let
    val n = size s
    val pos = Unsynchronized.ref 0
    fun peek () = if ! pos < n then SOME (String.sub (s, ! pos)) else NONE
    fun advance () = pos := ! pos + 1
    fun skip_ws () = (case peek () of SOME c => if Char.isSpace c then (advance (); skip_ws ()) else () | NONE => ())
    fun err msg = error ("urust_const_data: " ^ msg ^ " at offset " ^ string_of_int (! pos))
    fun expect c = (skip_ws (); if peek () = SOME c then advance () else err ("expected " ^ quote (str c)))
    fun is_name_char c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'" orelse c = #"."
    fun take_while p =
      let val start = ! pos
          fun go () = (case peek () of SOME c => if p c then (advance (); go ()) else () | NONE => ())
      in go (); String.substring (s, start, ! pos - start) end
    fun digits () =
      let val ds = take_while Char.isDigit
      in if ds = "" then err "expected digits"
         else fold (fn c => fn acc => acc * 10 + (Char.ord c - Char.ord #"0")) (String.explode ds) 0 end
    fun value () =
      (skip_ws ();
       case peek () of
         SOME #"[" => List (seq #"[" #"]")
       | SOME #"(" =>
           (case seq #"(" #")" of
              [] => Tuple []
            | [_] => err "a tuple has at least two components"
            | ds => Tuple ds)
       | SOME #"-" => (advance (); Int (~ (digits ())))
       | SOME c =>
           if Char.isDigit c then Int (digits ())
           else if is_name_char c then
             let val name = take_while is_name_char
             in skip_ws (); if peek () = SOME #"(" then App (name, seq #"(" #")") else App (name, []) end
           else err ("unexpected " ^ quote (str c))
       | NONE => err "unexpected end")
    and seq opn cls =
      let
        val _ = expect opn
        fun more acc =
          let val d = value () in
            skip_ws ();
            (case peek () of
              SOME c => if c = #"," then (advance (); more (d :: acc))
                        else if c = cls then (advance (); rev (d :: acc))
                        else err ("expected " ^ quote "," ^ " or " ^ quote (str cls))
            | NONE => err "unexpected end")
          end
      in skip_ws (); if peek () = SOME cls then (advance (); []) else more [] end
    val d = value ()
  in skip_ws (); if ! pos < n then err "trailing text" else d end

(*Local_Theory.define takes time superlinear in the depth of the term: a list longer than chunk
  is a balanced tree of appends (@) of lists of at most chunk elements, whose depth is
  logarithmic in its length*)
val chunk = 256

(*the term of type T given by d*)
fun elaborate ctxt T d =
  let
    val thy = Proof_Context.theory_of ctxt
    fun mk_list A ts =
      if length ts <= chunk then HOLogic.mk_list A ts
      else
        let
          val LT = HOLogic.listT A
          fun tree [l] = l
            | tree ls =
                let val (a, b) = chop (length ls div 2) ls
                in Const (\<^const_name>\<open>append\<close>, LT --> LT --> LT) $ tree a $ tree b end
        in tree (map (HOLogic.mk_list A) (chop_groups chunk ts)) end
    val consts = Unsynchronized.ref Symtab.empty
    fun const name =
      (case Symtab.lookup (! consts) name of
        SOME c => c
      | NONE =>
          let val c = Proof_Context.read_const {proper = true, strict = true} ctxt name
          in consts := Symtab.update (name, c) (! consts); c end)
    fun bad T what = error ("urust_const_data: " ^ what ^ " for the type " ^ Syntax.string_of_typ ctxt T)
    (*the term is not type-checked as a whole: a numeral needs a type of the numeral classes*)
    fun elab T (Int i) =
          if Sign.of_sort thy (T, if i < 0 then \<^sort>\<open>neg_numeral\<close> else \<^sort>\<open>{zero, numeral}\<close>)
          then HOLogic.mk_number T i else bad T ("the number " ^ string_of_int i)
      | elab T (List ds) =
          (case T of
            Type (\<^type_name>\<open>list\<close>, [A]) => mk_list A (map (elab A) ds)
          | _ => bad T "a list")
      | elab T (Tuple []) = if T = HOLogic.unitT then HOLogic.unit else bad T "()"
      | elab T (Tuple [d]) = elab T d
      | elab T (Tuple (d :: ds)) =
          (case T of
            Type (\<^type_name>\<open>prod\<close>, [A, B]) => HOLogic.mk_prod (elab A d, elab B (Tuple ds))
          | _ => bad T "a tuple")
      | elab T (App (name, ds)) =
          let
            val (c, cT) = dest_Const (const name)
            val k = length ds
            val argTs = take k (binder_types cT)
            val _ = if length argTs = k then () else error ("urust_const_data: too many arguments of " ^ quote name)
            val resT = funpow k range_type cT
            val tyenv = Sign.typ_match thy (resT, T) Vartab.empty
              handle Type.TYPE_MATCH => bad T ("the constant " ^ quote name ^ " of type " ^ Syntax.string_of_typ ctxt cT)
            val inst = Envir.subst_type tyenv
          in list_comb (Const (c, inst cT), map2 (fn A => elab (inst A)) argTs ds) end
  in elab T d end

fun const_data ((b, raw_T), raw_data) lthy =
  let
    val T = Syntax.read_typ lthy raw_T
    val vT =
      (case T of
        Type (\<^type_name>\<open>function_body\<close>, [_, vT, _, _, _]) => vT
      | _ => error "urust_const_data: the type is not a function_body type")
    val v = elaborate lthy vT (parse raw_data)
    val x = Free (singleton (Variable.variant_names lthy) ("x", vT))
    val template = Syntax.check_term lthy
      (Type.constraint T (Const (\<^const_name>\<open>FunctionBody\<close>, dummyT) $ (Const (\<^const_name>\<open>literal\<close>, dummyT) $ x)))
    val rhs = Term.subst_free [(x, v)] template
  in
    lthy |> Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), rhs)) |> snd
  end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>urust_const_data\<close>
    "define a uRust constant by its value, built from data without the inner syntax"
    (Parse.binding -- (\<^keyword>\<open>::\<close> |-- Parse.typ) -- (\<^keyword>\<open>=\<close> |-- Parse.embedded) >> const_data)

end
\<close>

text\<open>Example: a list of tuples (the frontend's tuples end with \<^const>\<open>TNil\<close>) with a negative number.\<close>

experiment
begin

urust_const_data "ex_table" :: \<open>('s, (32 sword \<times> bool \<times> tnil) list, 'abort, 'i, 'o) function_body\<close> =
  \<open>[(1, True, TNil), (-2, False, TNil)]\<close>

lemma \<open>ex_table = FunctionBody (literal [(1, True, TNil), (-2, False, TNil)])\<close>
  by (simp add: ex_table_def)

end

(*<*)
end
(*>*)
