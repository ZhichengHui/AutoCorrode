(*<*)
theory StdLib_Fmt
  imports Crush.Crush StdLib_References StdLib_Fmt_Text
begin
(*>*)

section\<open>Models of \<^verbatim>\<open>core::fmt\<close> for translated Rust\<close>

text\<open>
  A model of \<^verbatim>\<open>core::fmt::Formatter\<close> and of the formatting-trait implementations of the
  primitive types, ported from \<^verbatim>\<open>core::fmt\<close> (Rust nightly 2026-09-16) so that the output is
  the same string. The Rust frontend translates \<^verbatim>\<open>format!\<close>, \<^verbatim>\<open>write!\<close> and calls of these
  methods to the constants below.

  A formatter is its output so far (the buffer) together with the \<^verbatim>\<open>FormattingOptions\<close> of
  the placeholder being formatted: the flags word (bits 0--20: fill character; 21: \<^verbatim>\<open>+\<close>;
  22: \<^verbatim>\<open>-\<close>; 23: \<^verbatim>\<open>#\<close>; 24: \<^verbatim>\<open>0\<close>; 25: \<^verbatim>\<open>x?\<close>; 26: \<^verbatim>\<open>X?\<close>; 27: width set;
  28: precision set; 29--30: alignment, 0 left, 1 right, 2 center, 3 unset), the width and the
  precision.

  The output is a list of Unicode code points. Strings are \<^typ>\<open>String.literal\<close>, which holds
  ASCII characters only: when the output read as a \<^verbatim>\<open>String\<close> (\<^verbatim>\<open>format!\<close>) or a
  \<^verbatim>\<open>str\<close> written to it contains a character outside ASCII, or so does the fill character read
  as a \<^verbatim>\<open>char\<close>, the model aborts with \<^const>\<open>Unimplemented\<close> instead of producing a
  different string.
\<close>

subsection\<open>uRust functions\<close>

text\<open>\<^verbatim>\<open>FormattingOptions\<close> as given by a placeholder, with an empty buffer.\<close>
definition fmt_formatter_new :: \<open>32 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow>
      ('s, fmt_Formatter, 'abort, 'i, 'o) function_body\<close> where
  \<open>fmt_formatter_new fl w p \<equiv> FunctionBody (literal (fmt_opts fl w p))\<close>

text\<open>The output of a formatter as a string, and as code points.\<close>
definition fmt_formatter_buf :: \<open>fmt_Formatter \<Rightarrow> ('s, String.literal, 'abort, 'i, 'o) function_body\<close> where
  \<open>fmt_formatter_buf f \<equiv> FunctionBody (case fmt_lit (fmt_buf f) of
     Some s \<Rightarrow> literal s
   | None \<Rightarrow> unimplemented STR ''formatting: a string outside ASCII'')\<close>
definition fmt_formatter_codes :: \<open>fmt_Formatter \<Rightarrow> ('s, nat list, 'abort, 'i, 'o) function_body\<close> where
  \<open>fmt_formatter_codes f \<equiv> FunctionBody (literal (fmt_buf f))\<close>

text\<open>The option getters of \<^verbatim>\<open>Formatter\<close> (they take \<^verbatim>\<open>&self\<close>, a value).\<close>
definition fmt_alternate :: \<open>fmt_Formatter \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>fmt_alternate f \<equiv> FunctionBody (literal (fmt_flag f 23))\<close>
definition fmt_sign_plus :: \<open>fmt_Formatter \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>fmt_sign_plus f \<equiv> FunctionBody (literal (fmt_flag f 21))\<close>
definition fmt_sign_minus :: \<open>fmt_Formatter \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>fmt_sign_minus f \<equiv> FunctionBody (literal (fmt_flag f 22))\<close>
definition fmt_sign_aware_zero_pad :: \<open>fmt_Formatter \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>fmt_sign_aware_zero_pad f \<equiv> FunctionBody (literal (fmt_flag f 24))\<close>
definition fmt_width :: \<open>fmt_Formatter \<Rightarrow> ('s, 64 word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>fmt_width f \<equiv> FunctionBody (literal (if fmt_flag f 27 then Some (ucast (fmt_opt_width f)) else None))\<close>
definition fmt_precision :: \<open>fmt_Formatter \<Rightarrow> ('s, 64 word option, 'abort, 'i, 'o) function_body\<close> where
  \<open>fmt_precision f \<equiv> FunctionBody (literal (if fmt_flag f 28 then Some (ucast (fmt_opt_precision f)) else None))\<close>
definition fmt_fill :: \<open>fmt_Formatter \<Rightarrow> ('s, char, 'abort, 'i, 'o) function_body\<close> where
  \<open>fmt_fill f \<equiv> FunctionBody
     (if fmt_fill_code f < 128 then literal (char_of (fmt_fill_code f))
      else unimplemented STR ''formatting: fill character outside ASCII'')\<close>

context reference
begin

adhoc_overloading store_update_const \<rightleftharpoons> update_fun

text\<open>Appends the text \<open>g f\<close> computes from the formatter \<open>f\<close>.\<close>
definition fmt_emit :: \<open>('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow> (fmt_Formatter \<Rightarrow> nat list) \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_emit ptr g \<equiv> FunctionBody \<lbrakk>
     let fo = *ptr;
     ptr = \<llangle>fmt_append fo (g fo)\<rrangle>;
     Ok(())
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Formatter::write_str\<close> (of a string, or of code points: a literal outside ASCII, the
  output of another formatter), \<^verbatim>\<open>Formatter::write_char\<close>, \<^verbatim>\<open>Formatter::pad\<close>,
  \<^verbatim>\<open>Formatter::pad_integral\<close>.\<close>
definition fmt_write_str where \<open>fmt_write_str ptr s \<equiv> fmt_emit ptr (\<lambda>_. fmt_codes s)\<close>
definition fmt_write_codes where \<open>fmt_write_codes ptr cs \<equiv> fmt_emit ptr (\<lambda>_. cs)\<close>
definition fmt_write_char where \<open>fmt_write_char ptr c \<equiv> fmt_emit ptr (\<lambda>_. [of_char c])\<close>
definition fmt_pad where \<open>fmt_pad ptr s \<equiv> fmt_emit ptr (\<lambda>f. fmt_pad_codes f (fmt_codes s))\<close>
definition fmt_pad_integral where
  \<open>fmt_pad_integral ptr nonneg pfx digs \<equiv>
     fmt_emit ptr (\<lambda>f. fmt_pad_integral_codes f nonneg (fmt_codes pfx) (fmt_codes digs))\<close>

text\<open>The formatting-trait implementations of the primitive types.\<close>
definition fmt_Display_word :: \<open>'l::len word \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Display_word x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Display_word_text f x)\<close>
definition fmt_Display_sword :: \<open>'l::len sword \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Display_sword x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Display_sword_text f x)\<close>
definition fmt_Display_bool :: \<open>bool \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Display_bool x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Display_bool_text f x)\<close>
definition fmt_Display_char :: \<open>char \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Display_char x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Display_char_text f x)\<close>
definition fmt_Display_str :: \<open>String.literal \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Display_str x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Display_str_text f x)\<close>
definition fmt_Debug_word :: \<open>'l::len word \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Debug_word x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Debug_word_text f x)\<close>
definition fmt_Debug_sword :: \<open>'l::len sword \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Debug_sword x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Debug_sword_text f x)\<close>
definition fmt_Debug_bool :: \<open>bool \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Debug_bool x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Debug_bool_text f x)\<close>
definition fmt_Debug_char :: \<open>char \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Debug_char x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Debug_char_text f x)\<close>
definition fmt_Debug_str :: \<open>String.literal \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Debug_str x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Debug_str_text f x)\<close>
definition fmt_LowerHex_word :: \<open>'l::len word \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_LowerHex_word x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_LowerHex_word_text f x)\<close>
definition fmt_LowerHex_sword :: \<open>'l::len sword \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_LowerHex_sword x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_LowerHex_sword_text f x)\<close>
definition fmt_UpperHex_word :: \<open>'l::len word \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_UpperHex_word x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_UpperHex_word_text f x)\<close>
definition fmt_UpperHex_sword :: \<open>'l::len sword \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_UpperHex_sword x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_UpperHex_sword_text f x)\<close>
definition fmt_Octal_word :: \<open>'l::len word \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Octal_word x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Octal_word_text f x)\<close>
definition fmt_Octal_sword :: \<open>'l::len sword \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Octal_sword x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Octal_sword_text f x)\<close>
definition fmt_Binary_word :: \<open>'l::len word \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Binary_word x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Binary_word_text f x)\<close>
definition fmt_Binary_sword :: \<open>'l::len sword \<Rightarrow> ('a, 'b, fmt_Formatter) Global_Store.ref \<Rightarrow>
      ('s, (unit, fmt_Error) result, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>fmt_Binary_sword x ptr \<equiv> fmt_emit ptr (\<lambda>f. fmt_Binary_sword_text f x)\<close>

no_adhoc_overloading store_update_const \<rightleftharpoons> update_fun

end

(*<*)
end
(*>*)
