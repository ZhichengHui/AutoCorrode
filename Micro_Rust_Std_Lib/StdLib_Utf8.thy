(*<*)
theory StdLib_Utf8
  imports "HOL-Library.Word"
begin
(*>*)

section\<open>Unicode text: characters and UTF-8 strings\<close>

text\<open>
  The Rust frontend represents a \<^verbatim>\<open>char\<close> by its code point, a @{typ \<open>32 word\<close>} that is a
  Unicode scalar value (\<open>is_scalar\<close>), and a \<^verbatim>\<open>str\<close> or \<^verbatim>\<open>String\<close> by the bytes of its
  UTF-8 encoding, an @{typ \<open>8 word list\<close>} that is valid UTF-8 (\<open>utf8_valid\<close>). Both
  invariants hold of every value the translated code builds: literals, and the models below,
  which check them where Rust does (\<^verbatim>\<open>char::from_u32\<close>, \<^verbatim>\<open>str::from_utf8\<close>). The
  functions here are pure; they follow the implementation in \<^verbatim>\<open>core\<close> (Rust nightly
  2026-09-16).
\<close>

subsection\<open>Characters\<close>

definition is_scalar :: \<open>32 word \<Rightarrow> bool\<close> where
  \<open>is_scalar c \<equiv> c < 0xD800 \<or> (0xE000 \<le> c \<and> c < 0x110000)\<close>

text\<open>The character of a HOL (ASCII) character: the form of printable ASCII character literals.\<close>
definition char_code :: \<open>char \<Rightarrow> 32 word\<close> where
  \<open>char_code c \<equiv> of_nat (of_char c)\<close>

text\<open>The UTF-8 encoding of a character (\<^verbatim>\<open>char::encode_utf8\<close>).\<close>
definition char_utf8 :: \<open>32 word \<Rightarrow> 8 word list\<close> where
  \<open>char_utf8 c \<equiv> let n = unat c in
     if n < 0x80 then [of_nat n]
     else if n < 0x800 then [of_nat (0xC0 + n div 64), of_nat (0x80 + n mod 64)]
     else if n < 0x10000 then
       [of_nat (0xE0 + n div 4096), of_nat (0x80 + n div 64 mod 64), of_nat (0x80 + n mod 64)]
     else [of_nat (0xF0 + n div 262144), of_nat (0x80 + n div 4096 mod 64),
           of_nat (0x80 + n div 64 mod 64), of_nat (0x80 + n mod 64)]\<close>

text\<open>\<^verbatim>\<open>char::is_whitespace\<close>: Unicode \<open>White_Space\<close>.\<close>
definition char_is_whitespace :: \<open>32 word \<Rightarrow> bool\<close> where
  \<open>char_is_whitespace c \<equiv> (9 \<le> c \<and> c \<le> 13) \<or> c = 32 \<or> c = 0x85 \<or> c = 0xA0 \<or> c = 0x1680
     \<or> (0x2000 \<le> c \<and> c \<le> 0x200A) \<or> c = 0x2028 \<or> c = 0x2029 \<or> c = 0x202F \<or> c = 0x205F
     \<or> c = 0x3000\<close>

text\<open>\<^verbatim>\<open>char::is_control\<close>: the general category \<open>Cc\<close>.\<close>
definition char_is_control :: \<open>32 word \<Rightarrow> bool\<close> where
  \<open>char_is_control c \<equiv> c \<le> 0x1F \<or> (0x7F \<le> c \<and> c \<le> 0x9F)\<close>

text\<open>The ASCII classes of \<^verbatim>\<open>u8\<close> and \<^verbatim>\<open>char\<close> (\<^verbatim>\<open>is_ascii_digit\<close>, ...), on the code.\<close>
definition ascii_is_uppercase :: \<open>nat \<Rightarrow> bool\<close> where \<open>ascii_is_uppercase n \<equiv> 65 \<le> n \<and> n \<le> 90\<close>
definition ascii_is_lowercase :: \<open>nat \<Rightarrow> bool\<close> where \<open>ascii_is_lowercase n \<equiv> 97 \<le> n \<and> n \<le> 122\<close>
definition ascii_is_alphabetic :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>ascii_is_alphabetic n \<equiv> ascii_is_uppercase n \<or> ascii_is_lowercase n\<close>
definition ascii_is_digit :: \<open>nat \<Rightarrow> bool\<close> where \<open>ascii_is_digit n \<equiv> 48 \<le> n \<and> n \<le> 57\<close>
definition ascii_is_alphanumeric :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>ascii_is_alphanumeric n \<equiv> ascii_is_alphabetic n \<or> ascii_is_digit n\<close>
definition ascii_is_hexdigit :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>ascii_is_hexdigit n \<equiv> ascii_is_digit n \<or> (65 \<le> n \<and> n \<le> 70) \<or> (97 \<le> n \<and> n \<le> 102)\<close>
definition ascii_is_whitespace :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>ascii_is_whitespace n \<equiv> n \<in> {9, 10, 12, 13, 32}\<close>
definition ascii_is_control :: \<open>nat \<Rightarrow> bool\<close> where \<open>ascii_is_control n \<equiv> n \<le> 31 \<or> n = 127\<close>
definition ascii_is_graphic :: \<open>nat \<Rightarrow> bool\<close> where \<open>ascii_is_graphic n \<equiv> 33 \<le> n \<and> n \<le> 126\<close>
definition ascii_is_punctuation :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>ascii_is_punctuation n \<equiv> ascii_is_graphic n \<and> \<not> ascii_is_alphanumeric n\<close>

text\<open>\<^verbatim>\<open>to_ascii_uppercase\<close>, \<^verbatim>\<open>to_ascii_lowercase\<close>: other values are kept.\<close>
definition ascii_upper :: \<open>'l::len word \<Rightarrow> 'l word\<close> where
  \<open>ascii_upper c \<equiv> if ascii_is_lowercase (unat c) then c - 32 else c\<close>
definition ascii_lower :: \<open>'l::len word \<Rightarrow> 'l word\<close> where
  \<open>ascii_lower c \<equiv> if ascii_is_uppercase (unat c) then c + 32 else c\<close>

text\<open>\<^verbatim>\<open>char::to_digit(radix)\<close> for a radix from 2 to 36: letters of either case are the digits
  from 10 on, other values are 36 or more (the wrapping subtraction and the mask of
  \<^verbatim>\<open>core\<close>).\<close>
definition char_digit_value :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> 32 word\<close> where
  \<open>char_digit_value c radix \<equiv>
     if c > 57 \<and> radix > 10 then
       (let x = unat (c - 65) in of_nat (x - x div 32 mod 2 * 32) + 10)
     else c - 48\<close>

subsection\<open>UTF-8\<close>

definition utf8_cont :: \<open>8 word \<Rightarrow> bool\<close> where
  \<open>utf8_cont b \<equiv> 0x80 \<le> b \<and> b \<le> 0xBF\<close>

text\<open>\<^verbatim>\<open>core::str::utf8_char_width\<close>: the length of the sequence a byte starts, 0 for a byte
  that starts none.\<close>
definition utf8_width :: \<open>8 word \<Rightarrow> nat\<close> where
  \<open>utf8_width b \<equiv> if b < 0x80 then 1 else if 0xC2 \<le> b \<and> b \<le> 0xDF then 2
     else if 0xE0 \<le> b \<and> b \<le> 0xEF then 3 else if 0xF0 \<le> b \<and> b \<le> 0xF4 then 4 else 0\<close>

text\<open>The allowed second bytes after the first byte \<open>b\<close> (no overlong forms, no surrogates, nothing
  beyond U+10FFFF).\<close>
definition utf8_second_ok :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> bool\<close> where
  \<open>utf8_second_ok b c \<equiv>
     if b = 0xE0 then 0xA0 \<le> c \<and> c \<le> 0xBF
     else if b = 0xED then 0x80 \<le> c \<and> c \<le> 0x9F
     else if b = 0xF0 then 0x90 \<le> c \<and> c \<le> 0xBF
     else if b = 0xF4 then 0x80 \<le> c \<and> c \<le> 0x8F
     else utf8_cont c\<close>

text\<open>\<^verbatim>\<open>core::str::validations::run_utf8_validation\<close> on the bytes from offset \<open>i\<close>:
  \<^const>\<open>None\<close> if they are valid UTF-8, else \<open>Some (valid_up_to, error_len)\<close>, where
  \<open>error_len\<close> is \<^const>\<open>None\<close> when the input ends inside a sequence that could still be
  completed, and otherwise the length of the invalid sequence (1 to 3).\<close>
fun utf8_check :: \<open>nat \<Rightarrow> 8 word list \<Rightarrow> (nat \<times> 8 word option) option\<close> where
  \<open>utf8_check i [] = None\<close>
| \<open>utf8_check i (b # bs) =
    (let w = utf8_width b in
     if w = 1 then utf8_check (i + 1) bs
     else if w = 0 then Some (i, Some 1)
     else (case bs of
       [] \<Rightarrow> Some (i, None)
     | c # bs2 \<Rightarrow>
         if \<not> utf8_second_ok b c then Some (i, Some 1)
         else if w = 2 then utf8_check (i + 2) bs2
         else (case bs2 of
           [] \<Rightarrow> Some (i, None)
         | d # bs3 \<Rightarrow>
             if \<not> utf8_cont d then Some (i, Some 2)
             else if w = 3 then utf8_check (i + 3) bs3
             else (case bs3 of
               [] \<Rightarrow> Some (i, None)
             | e # bs4 \<Rightarrow> if \<not> utf8_cont e then Some (i, Some 3) else utf8_check (i + 4) bs4))))\<close>

definition utf8_valid :: \<open>8 word list \<Rightarrow> bool\<close> where
  \<open>utf8_valid s \<equiv> utf8_check 0 s = None\<close>

text\<open>The value of the continuation byte at position \<open>i\<close> (0 past the end).\<close>
definition utf8_cont_at :: \<open>8 word list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>utf8_cont_at bs i \<equiv> if i < length bs then unat (bs ! i) mod 64 else 0\<close>

text\<open>The characters of a valid UTF-8 string (\<^verbatim>\<open>str::chars\<close>).\<close>
fun utf8_decode :: \<open>8 word list \<Rightarrow> 32 word list\<close> where
  \<open>utf8_decode [] = []\<close>
| \<open>utf8_decode (b # bs) =
    (let n = unat b in
     if n < 0x80 then of_nat n # utf8_decode bs
     else if n < 0xE0 then of_nat (n mod 32 * 64 + utf8_cont_at bs 0) # utf8_decode (drop 1 bs)
     else if n < 0xF0 then
       of_nat (n mod 16 * 4096 + utf8_cont_at bs 0 * 64 + utf8_cont_at bs 1) # utf8_decode (drop 2 bs)
     else of_nat (n mod 8 * 262144 + utf8_cont_at bs 0 * 4096 + utf8_cont_at bs 1 * 64
                  + utf8_cont_at bs 2) # utf8_decode (drop 3 bs))\<close>

definition utf8_encode :: \<open>32 word list \<Rightarrow> 8 word list\<close> where
  \<open>utf8_encode cs \<equiv> List.concat (List.map char_utf8 cs)\<close>

text\<open>A string literal: the bytes of an ASCII \<^typ>\<open>String.literal\<close> (other characters of a
  literal are written with \<^const>\<open>char_utf8\<close>).\<close>
definition str_lit :: \<open>String.literal \<Rightarrow> 8 word list\<close> where
  \<open>str_lit s \<equiv> List.map (\<lambda>c. of_nat (of_char c)) (String.explode s)\<close>

text\<open>\<^verbatim>\<open>str::is_char_boundary\<close>.\<close>
definition str_is_char_boundary :: \<open>8 word list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>str_is_char_boundary s i \<equiv> i = 0 \<or> i = length s \<or> (i < length s \<and> \<not> utf8_cont (s ! i))\<close>

text\<open>A string as an abort message: its ASCII bytes, other bytes as \<open>?\<close>.\<close>
definition str_message :: \<open>8 word list \<Rightarrow> String.literal\<close> where
  \<open>str_message s \<equiv> String.implode (List.map (\<lambda>b. if b < 128 then char_of (unat b) else CHR ''?'') s)\<close>

text\<open>The lexicographic order of byte strings (\<^verbatim>\<open>Ord\<close> on \<^verbatim>\<open>str\<close>): \<open>-1\<close>, \<open>0\<close>, \<open>1\<close>.\<close>
fun bytes_cmp :: \<open>8 word list \<Rightarrow> 8 word list \<Rightarrow> int\<close> where
  \<open>bytes_cmp [] [] = 0\<close>
| \<open>bytes_cmp [] _ = -1\<close>
| \<open>bytes_cmp _ [] = 1\<close>
| \<open>bytes_cmp (a # as) (b # bs) = (if a < b then -1 else if b < a then 1 else bytes_cmp as bs)\<close>

text\<open>\<^verbatim>\<open>core::str::Utf8Error\<close>: \<^verbatim>\<open>valid_up_to\<close>, \<^verbatim>\<open>error_len\<close> (see \<^const>\<open>utf8_check\<close>).\<close>
datatype utf8_error = Utf8Error (utf8_error_valid_up_to: \<open>64 word\<close>) (utf8_error_len: \<open>8 word option\<close>)

subsection\<open>Tests\<close>

lemma \<open>char_utf8 0x41 = [0x41]\<close> \<open>char_utf8 0xE9 = [0xC3, 0xA9]\<close> \<open>char_utf8 0x20AC = [0xE2, 0x82, 0xAC]\<close>
  \<open>char_utf8 0x1F600 = [0xF0, 0x9F, 0x98, 0x80]\<close> \<open>char_utf8 0x10FFFF = [0xF4, 0x8F, 0xBF, 0xBF]\<close>
  by (simp_all add: char_utf8_def)

lemma \<open>utf8_decode [0x61, 0xC3, 0xA9, 0xE2, 0x82, 0xAC, 0xF0, 0x9F, 0x98, 0x80] = [0x61, 0xE9, 0x20AC, 0x1F600]\<close>
  by (simp add: utf8_cont_at_def)

text\<open>The error positions and lengths of \<^verbatim>\<open>from_utf8\<close> (as Rust reports them).\<close>
lemma \<open>utf8_check 0 [0x61, 0xC3, 0xA9] = None\<close>
  \<open>utf8_check 0 [0x61, 0xFF] = Some (1, Some 1)\<close>
  \<open>utf8_check 0 [0x61, 0xE2, 0x82] = Some (1, None)\<close>
  \<open>utf8_check 0 [0xE2, 0x28, 0xA1] = Some (0, Some 1)\<close>
  \<open>utf8_check 0 [0xE2, 0x82, 0x28] = Some (0, Some 2)\<close>
  \<open>utf8_check 0 [0xF0, 0x9F, 0x98, 0x28] = Some (0, Some 3)\<close>
  \<open>utf8_check 0 [0xED, 0xA0, 0x80] = Some (0, Some 1)\<close>
  \<open>utf8_check 0 [0xC0, 0x80] = Some (0, Some 1)\<close>
  by (simp_all add: utf8_width_def utf8_second_ok_def utf8_cont_def)

lemma \<open>char_digit_value 0x37 10 = 7\<close> \<open>char_digit_value 0x66 16 = 15\<close> \<open>char_digit_value 0x46 16 = 15\<close>
  \<open>char_digit_value 0x5A 36 = 35\<close> \<open>char_digit_value 0x7B 36 \<ge> 36\<close>
  by (simp_all add: char_digit_value_def)

(*<*)
end
(*>*)
