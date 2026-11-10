(*<*)
theory StdLib_Fmt_Text
  imports "HOL-Library.Word" "Word_Lib.Signed_Words"
begin
(*>*)

section\<open>The text produced by \<^verbatim>\<open>core::fmt\<close>\<close>

text\<open>Pure functions computing what the models in \<^verbatim>\<open>StdLib_Fmt\<close> append to a formatter's
  buffer; see there. They are kept apart from the uRust syntax.\<close>

datatype fmt_Error = fmt_Error

datatype fmt_Formatter =
  fmt_Formatter_mk (fmt_buf: String.literal) (fmt_opt_flags: \<open>32 word\<close>) (fmt_opt_width: \<open>16 word\<close>)
    (fmt_opt_precision: \<open>16 word\<close>)

subsection\<open>Pure functions\<close>

definition fmt_codes :: \<open>String.literal \<Rightarrow> nat list\<close> where
  \<open>fmt_codes s \<equiv> List.map of_char (String.explode s)\<close>

text\<open>The string of a list of code points; \<^term>\<open>None\<close> if one is outside ASCII.\<close>
definition fmt_lit :: \<open>nat list \<Rightarrow> String.literal option\<close> where
  \<open>fmt_lit xs \<equiv> if List.list_all (\<lambda>c. c < 128) xs then Some (String.implode (List.map char_of xs)) else None\<close>

definition fmt_flag :: \<open>fmt_Formatter \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>fmt_flag f n \<equiv> bit (fmt_opt_flags f) n\<close>

definition fmt_fill_code :: \<open>fmt_Formatter \<Rightarrow> nat\<close> where
  \<open>fmt_fill_code f \<equiv> unat (take_bit 21 (fmt_opt_flags f))\<close>

text\<open>The alignment: 0 left, 1 right, 2 center, 3 unset.\<close>
definition fmt_align :: \<open>fmt_Formatter \<Rightarrow> nat\<close> where
  \<open>fmt_align f \<equiv> unat (take_bit 2 (drop_bit 29 (fmt_opt_flags f)))\<close>

text\<open>\<^verbatim>\<open>Formatter::padding(padding, default)\<close>: the number of fill characters
  before the text (the rest of the \<open>padding\<close> ones come after it).\<close>
definition fmt_padding_before :: \<open>fmt_Formatter \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>fmt_padding_before f padding dflt \<equiv>
     let al = (if fmt_align f = 3 then dflt else fmt_align f)
     in if al = 0 then 0 else if al = 1 then padding else padding div 2\<close>

text\<open>The text \<open>s\<close> padded to \<open>padding\<close> more characters.\<close>
definition fmt_padded :: \<open>fmt_Formatter \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>fmt_padded f padding dflt s \<equiv>
     List.replicate (fmt_padding_before f padding dflt) (fmt_fill_code f) @ s @
     List.replicate (padding - fmt_padding_before f padding dflt) (fmt_fill_code f)\<close>

text\<open>\<^verbatim>\<open>Formatter::pad(s)\<close>.\<close>
definition fmt_pad_codes :: \<open>fmt_Formatter \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>fmt_pad_codes f s \<equiv>
     if \<not> fmt_flag f 27 \<and> \<not> fmt_flag f 28 then s
     else
       let s' = (if fmt_flag f 28 then List.take (unat (fmt_opt_precision f)) s else s)
       in if List.length s' < unat (fmt_opt_width f) then
            fmt_padded f (unat (fmt_opt_width f) - List.length s') 0 s'
          else s'\<close>

text\<open>\<^verbatim>\<open>Formatter::pad_integral(is_nonnegative, prefix, buf)\<close>.\<close>
definition fmt_pad_integral_codes :: \<open>fmt_Formatter \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>fmt_pad_integral_codes f nonneg prefix digits \<equiv>
     let sign = (if \<not> nonneg then [of_char CHR ''-''] else if fmt_flag f 21 then [of_char CHR ''+''] else []);
         prefix' = (if fmt_flag f 23 then prefix else []);
         width = List.length digits + List.length sign + List.length prefix';
         min = unat (fmt_opt_width f)
     in if min \<le> width then sign @ prefix' @ digits
        else if fmt_flag f 24 then sign @ prefix' @ List.replicate (min - width) (of_char CHR ''0'') @ digits
        else fmt_padded f (min - width) 1 (sign @ prefix' @ digits)\<close>

definition fmt_digit :: \<open>bool \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>fmt_digit upper d \<equiv> if d < 10 then 48 + d else (if upper then 55 else 87) + d\<close>

text\<open>The digits of \<open>n\<close> in base \<open>b\<close> (most significant first, no leading zeros, \<open>0\<close> for zero).\<close>
fun fmt_digits :: \<open>nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>fmt_digits b upper n =
     (if b \<le> 1 \<or> n < b then [fmt_digit upper n] else fmt_digits b upper (n div b) @ [fmt_digit upper (n mod b)])\<close>

text\<open>Display of an integer of absolute value \<open>n\<close>.\<close>
definition fmt_display_int_codes :: \<open>fmt_Formatter \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>fmt_display_int_codes f nonneg n \<equiv> fmt_pad_integral_codes f nonneg [] (fmt_digits 10 False n)\<close>

text\<open>The radix traits on the (two's-complement) bit pattern \<open>n\<close>: \<open>radix\<close> 16, 8 or 2.\<close>
definition fmt_radix_codes :: \<open>fmt_Formatter \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>fmt_radix_codes f radix upper n \<equiv>
     fmt_pad_integral_codes f True
       (fmt_codes (if radix = 16 then STR ''0x'' else if radix = 8 then STR ''0o'' else STR ''0b''))
       (fmt_digits radix upper n)\<close>

text\<open>Debug of an integer: the radix trait selected by the \<^verbatim>\<open>x?\<close>/\<^verbatim>\<open>X?\<close> flags, else Display.\<close>
definition fmt_debug_int_codes :: \<open>fmt_Formatter \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>fmt_debug_int_codes f nonneg n bits \<equiv>
     if fmt_flag f 25 then fmt_radix_codes f 16 False bits
     else if fmt_flag f 26 then fmt_radix_codes f 16 True bits
     else fmt_display_int_codes f nonneg n\<close>

text\<open>\<^verbatim>\<open>char::escape_debug_ext\<close> on a code point, for \<^verbatim>\<open>str\<close> (\<open>in_str\<close>: escape \<^verbatim>\<open>"\<close>)
  or \<^verbatim>\<open>char\<close> (escape \<^verbatim>\<open>'\<close>). A code point from U+0080 on is kept (its escape depends on
  Unicode properties), which makes the result non-ASCII.\<close>
definition fmt_escape_debug :: \<open>bool \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>fmt_escape_debug in_str c \<equiv>
     if c = 34 \<and> in_str then [92, 34]
     else if c = 39 \<and> \<not> in_str then [92, 39]
     else if c = 92 then [92, 92]
     else if c = 10 then [92, 110]
     else if c = 9 then [92, 116]
     else if c = 13 then [92, 114]
     else if c = 0 then [92, 48]
     else if 32 \<le> c \<and> c \<le> 126 then [c]
     else if c < 128 then [92, 117, 123] @ fmt_digits 16 False c @ [125]
     else [c]\<close>

definition fmt_debug_str_codes :: \<open>nat list \<Rightarrow> nat list\<close> where
  \<open>fmt_debug_str_codes s \<equiv> [34] @ List.concat (List.map (fmt_escape_debug True) s) @ [34]\<close>

definition fmt_debug_char_codes :: \<open>nat \<Rightarrow> nat list\<close> where
  \<open>fmt_debug_char_codes c \<equiv> [39] @ fmt_escape_debug False c @ [39]\<close>

definition fmt_display_char_codes :: \<open>fmt_Formatter \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>fmt_display_char_codes f c \<equiv> if \<not> fmt_flag f 27 \<and> \<not> fmt_flag f 28 then [c] else fmt_pad_codes f [c]\<close>

definition fmt_bool_codes :: \<open>fmt_Formatter \<Rightarrow> bool \<Rightarrow> nat list\<close> where
  \<open>fmt_bool_codes f b \<equiv> fmt_pad_codes f (fmt_codes (if b then STR ''true'' else STR ''false''))\<close>

text\<open>The text a formatting-trait implementation appends, for a formatter with an empty buffer
  built from the options; used to test the model against Rust.\<close>
definition fmt_opts :: \<open>32 word \<Rightarrow> 16 word \<Rightarrow> 16 word \<Rightarrow> fmt_Formatter\<close> where
  \<open>fmt_opts fl w p \<equiv> fmt_Formatter_mk STR '''' fl w p\<close>

definition fmt_append :: \<open>fmt_Formatter \<Rightarrow> String.literal \<Rightarrow> fmt_Formatter\<close> where
  \<open>fmt_append f s \<equiv> case f of fmt_Formatter_mk b fl w p \<Rightarrow> fmt_Formatter_mk (b + s) fl w p\<close>

text\<open>The text appended by the formatting-trait implementations of the primitive types
  (\<^term>\<open>None\<close>: not ASCII).\<close>
definition fmt_Display_word_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len word \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Display_word_text f x \<equiv> fmt_lit (fmt_display_int_codes f True (unat x))\<close>
definition fmt_Display_sword_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len sword \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Display_sword_text f x \<equiv> fmt_lit (fmt_display_int_codes f (0 \<le> sint x) (nat \<bar>sint x\<bar>))\<close>
definition fmt_Display_bool_text :: \<open>fmt_Formatter \<Rightarrow> bool \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Display_bool_text f x \<equiv> fmt_lit (fmt_bool_codes f x)\<close>
definition fmt_Display_char_text :: \<open>fmt_Formatter \<Rightarrow> char \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Display_char_text f x \<equiv> fmt_lit (fmt_display_char_codes f (of_char x))\<close>
definition fmt_Display_str_text :: \<open>fmt_Formatter \<Rightarrow> String.literal \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Display_str_text f x \<equiv> fmt_lit (fmt_pad_codes f (fmt_codes x))\<close>
definition fmt_Debug_word_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len word \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Debug_word_text f x \<equiv> fmt_lit (fmt_debug_int_codes f True (unat x) (unat x))\<close>
definition fmt_Debug_sword_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len sword \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Debug_sword_text f x \<equiv> fmt_lit (fmt_debug_int_codes f (0 \<le> sint x) (nat \<bar>sint x\<bar>) (unat x))\<close>
definition fmt_Debug_bool_text :: \<open>fmt_Formatter \<Rightarrow> bool \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Debug_bool_text f x \<equiv> fmt_lit (fmt_bool_codes f x)\<close>
definition fmt_Debug_char_text :: \<open>fmt_Formatter \<Rightarrow> char \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Debug_char_text f x \<equiv> fmt_lit (fmt_debug_char_codes (of_char x))\<close>
definition fmt_Debug_str_text :: \<open>fmt_Formatter \<Rightarrow> String.literal \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Debug_str_text f x \<equiv> fmt_lit (fmt_debug_str_codes (fmt_codes x))\<close>
definition fmt_LowerHex_word_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len word \<Rightarrow> String.literal option\<close> where
  \<open>fmt_LowerHex_word_text f x \<equiv> fmt_lit (fmt_radix_codes f 16 False (unat x))\<close>
definition fmt_LowerHex_sword_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len sword \<Rightarrow> String.literal option\<close> where
  \<open>fmt_LowerHex_sword_text f x \<equiv> fmt_lit (fmt_radix_codes f 16 False (unat x))\<close>
definition fmt_UpperHex_word_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len word \<Rightarrow> String.literal option\<close> where
  \<open>fmt_UpperHex_word_text f x \<equiv> fmt_lit (fmt_radix_codes f 16 True (unat x))\<close>
definition fmt_UpperHex_sword_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len sword \<Rightarrow> String.literal option\<close> where
  \<open>fmt_UpperHex_sword_text f x \<equiv> fmt_lit (fmt_radix_codes f 16 True (unat x))\<close>
definition fmt_Octal_word_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len word \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Octal_word_text f x \<equiv> fmt_lit (fmt_radix_codes f 8 False (unat x))\<close>
definition fmt_Octal_sword_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len sword \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Octal_sword_text f x \<equiv> fmt_lit (fmt_radix_codes f 8 False (unat x))\<close>
definition fmt_Binary_word_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len word \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Binary_word_text f x \<equiv> fmt_lit (fmt_radix_codes f 2 False (unat x))\<close>
definition fmt_Binary_sword_text :: \<open>fmt_Formatter \<Rightarrow> 'l::len sword \<Rightarrow> String.literal option\<close> where
  \<open>fmt_Binary_sword_text f x \<equiv> fmt_lit (fmt_radix_codes f 2 False (unat x))\<close>

(*<*)
end
(*>*)
