(*<*)
theory StdLib_Vec
  imports "Micro_Rust_Std_Lib.StdLib_References" Crush.Crush Misc.Result
begin
(*>*)

section\<open>A value model of \<^verbatim>\<open>Vec<T>\<close> with capacity\<close>

text\<open>
  A model of \<^verbatim>\<open>alloc::vec::Vec<T>\<close> as a value: its elements, its capacity, and the layout
  (size and alignment) of \<^verbatim>\<open>T\<close>. The model has the length bound of a \<^verbatim>\<open>Vec\<close>, its
  capacity, and its \<^verbatim>\<open>capacity overflow\<close> panics. It has no addresses: the buffer is not
  in the store, so a reallocation is not visible, and an allocation failure (which aborts the
  process in Rust) is not modelled.

  The layout is part of the value, not a type class on the element type: the Rust frontend maps
  \<^verbatim>\<open>&T\<close>, \<^verbatim>\<open>Box<T>\<close> and \<^verbatim>\<open>T\<close> to the same HOL type, and their sizes differ. The
  code that creates a vector gives the layout (the frontend takes it from rustc).

  The standard library does not specify how much the capacity grows, nor the exact capacity
  that \<^verbatim>\<open>with_capacity\<close>, \<^verbatim>\<open>reserve_exact\<close>, \<^verbatim>\<open>shrink_to_fit\<close> and \<^verbatim>\<open>clone\<close> give.
  The model leaves these values unspecified (@{term Eps}): a proof can use only their bounds.
  An unspecified value is still a function of its arguments, so the model is an
  over-approximation of every deterministic growth strategy within these bounds.
\<close>

subsection\<open>Layouts and the capacity bound\<close>

datatype_record elem_layout =
  layout_size :: nat
  layout_align :: nat

definition isize_max :: nat where
  \<open>isize_max \<equiv> 2 ^ 63 - 1\<close>

definition usize_max :: nat where
  \<open>usize_max \<equiv> 2 ^ 64 - 1\<close>

text\<open>The largest capacity of a vector of elements of layout \<open>l\<close>: \<^verbatim>\<open>Layout::array\<close>
  requires \<open>n * size \<le> isize::MAX - (align - 1)\<close>. A vector of zero-sized elements has the
  capacity \<^verbatim>\<open>usize::MAX\<close>.\<close>
definition rvec_cap_max :: \<open>elem_layout \<Rightarrow> nat\<close> where
  \<open>rvec_cap_max l \<equiv> if layout_size l = 0 then usize_max
     else (isize_max - (layout_align l - 1)) div layout_size l\<close>

text\<open>The smallest non-zero capacity that the amortised growth gives (\<^verbatim>\<open>RawVec::MIN_NON_ZERO_CAP\<close>).\<close>
definition rvec_min_non_zero_cap :: \<open>elem_layout \<Rightarrow> nat\<close> where
  \<open>rvec_min_non_zero_cap l \<equiv> if layout_size l = 1 then 8 else if layout_size l \<le> 1024 then 4 else 1\<close>

lemma rvec_cap_max_le_usize_max:
  shows \<open>rvec_cap_max l \<le> usize_max\<close>
  by (auto simp add: rvec_cap_max_def isize_max_def usize_max_def intro: le_trans[OF div_le_dividend])

subsection\<open>The vector type\<close>

datatype_record 'v rvec =
  rvec_elems :: \<open>'v list\<close>
  rvec_cap :: nat
  rvec_layout :: elem_layout

text\<open>The invariant of a \<^verbatim>\<open>Vec\<close>. It is not part of the type: the focus on the elements
  (the \<^verbatim>\<open>Deref\<close> to a slice) must accept a list of any length.\<close>
definition rvec_wf :: \<open>'v rvec \<Rightarrow> bool\<close> where
  \<open>rvec_wf v \<equiv> length (rvec_elems v) \<le> rvec_cap v \<and> rvec_cap v \<le> rvec_cap_max (rvec_layout v) \<and>
     (layout_size (rvec_layout v) = 0 \<longrightarrow> rvec_cap v = usize_max)\<close>

abbreviation rvec_length :: \<open>'v rvec \<Rightarrow> nat\<close> where
  \<open>rvec_length v \<equiv> length (rvec_elems v)\<close>

lemma rvec_wf_length_bound:
  assumes \<open>rvec_wf v\<close>
  shows \<open>rvec_length v < 2 ^ 64\<close> and \<open>rvec_cap v < 2 ^ 64\<close>
  using assms rvec_cap_max_le_usize_max[of \<open>rvec_layout v\<close>]
  by (auto simp add: rvec_wf_def usize_max_def)

text\<open>A vector of a layout with the given elements and, for a sized element, the capacity \<open>c\<close>.\<close>
definition rvec_make :: \<open>elem_layout \<Rightarrow> 'v list \<Rightarrow> nat \<Rightarrow> 'v rvec\<close> where
  \<open>rvec_make l xs c \<equiv> make_rvec xs (if layout_size l = 0 then usize_max else c) l\<close>

lemma rvec_make_components [simp]:
  shows \<open>rvec_elems (rvec_make l xs c) = xs\<close>
    and \<open>rvec_layout (rvec_make l xs c) = l\<close>
    and \<open>rvec_cap (rvec_make l xs c) = (if layout_size l = 0 then usize_max else c)\<close>
  by (auto simp add: rvec_make_def)

lemma rvec_make_wf:
  assumes \<open>length xs \<le> c\<close> and \<open>c \<le> rvec_cap_max l\<close>
  shows \<open>rvec_wf (rvec_make l xs c)\<close>
  using assms
  by (auto simp add: rvec_wf_def rvec_cap_max_def usize_max_def)

subsection\<open>Unspecified capacities\<close>

text\<open>The capacity of a new allocation for at least \<open>n\<close> elements (\<^verbatim>\<open>with_capacity\<close>,
  \<^verbatim>\<open>reserve_exact\<close>, \<^verbatim>\<open>clone\<close>): at least \<open>n\<close>, and within the bound.\<close>
definition rvec_alloc_cap :: \<open>elem_layout \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>rvec_alloc_cap l n \<equiv> SOME m. n \<le> m \<and> m \<le> rvec_cap_max l\<close>

lemma rvec_alloc_cap_bounds:
  assumes \<open>n \<le> rvec_cap_max l\<close>
  shows \<open>n \<le> rvec_alloc_cap l n\<close> and \<open>rvec_alloc_cap l n \<le> rvec_cap_max l\<close>
  using someI[of \<open>\<lambda>m. n \<le> m \<and> m \<le> rvec_cap_max l\<close> n] assms
  by (auto simp add: rvec_alloc_cap_def)

text\<open>The capacity after an amortised growth from the capacity \<open>c\<close> to at least \<open>n\<close> elements
  (\<^verbatim>\<open>push\<close>, \<^verbatim>\<open>reserve\<close>, \<^verbatim>\<open>insert\<close>, \<^verbatim>\<open>extend_from_slice\<close>, \<^verbatim>\<open>resize\<close>): at least
  \<open>n\<close>, and at most the capacity of the current strategy (doubling, at least the minimum
  non-zero capacity). It may exceed the bound: then the operation panics.\<close>
definition rvec_grow_cap :: \<open>elem_layout \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>rvec_grow_cap l c n \<equiv> SOME m. n \<le> m \<and> m \<le> max (2 * c) (max n (rvec_min_non_zero_cap l))\<close>

lemma rvec_grow_cap_bounds:
  shows \<open>n \<le> rvec_grow_cap l c n\<close>
    and \<open>rvec_grow_cap l c n \<le> max (2 * c) (max n (rvec_min_non_zero_cap l))\<close>
  using someI[of \<open>\<lambda>m. n \<le> m \<and> m \<le> max (2 * c) (max n (rvec_min_non_zero_cap l))\<close> n]
  by (auto simp add: rvec_grow_cap_def)

text\<open>The capacity after shrinking the capacity \<open>c\<close> towards \<open>n \<le> c\<close>
  (\<^verbatim>\<open>shrink_to_fit\<close>, \<^verbatim>\<open>shrink_to\<close>): between the two.\<close>
definition rvec_shrink_cap :: \<open>elem_layout \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>rvec_shrink_cap l c n \<equiv> SOME m. n \<le> m \<and> m \<le> c\<close>

lemma rvec_shrink_cap_bounds:
  assumes \<open>n \<le> c\<close>
  shows \<open>n \<le> rvec_shrink_cap l c n\<close> and \<open>rvec_shrink_cap l c n \<le> c\<close>
  using someI[of \<open>\<lambda>m. n \<le> m \<and> m \<le> c\<close> n] assms
  by (auto simp add: rvec_shrink_cap_def)

subsection\<open>The operations on values\<close>

text\<open>Each operation that can panic is a function to an option: \<^term>\<open>None\<close> is the panic.\<close>

text\<open>\<^verbatim>\<open>Vec::new()\<close>.\<close>
definition rvec_new_val :: \<open>elem_layout \<Rightarrow> 'v rvec\<close> where
  \<open>rvec_new_val l \<equiv> rvec_make l [] 0\<close>

text\<open>\<^verbatim>\<open>Vec::with_capacity(n)\<close>: panics if \<open>n\<close> exceeds the bound.\<close>
definition rvec_with_capacity_val :: \<open>elem_layout \<Rightarrow> nat \<Rightarrow> 'v rvec option\<close> where
  \<open>rvec_with_capacity_val l n \<equiv>
     if n \<le> rvec_cap_max l then Some (rvec_make l [] (rvec_alloc_cap l n)) else None\<close>

text\<open>\<^verbatim>\<open>vec![x; n]\<close> (\<^verbatim>\<open>alloc::vec::from_elem\<close>): \<^verbatim>\<open>with_capacity(n)\<close>, then the copies.\<close>
definition rvec_from_elem_val :: \<open>elem_layout \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'v rvec option\<close> where
  \<open>rvec_from_elem_val l x n \<equiv>
     if n \<le> rvec_cap_max l then Some (rvec_make l (replicate n x) (rvec_alloc_cap l n)) else None\<close>

text\<open>\<^verbatim>\<open>vec![x1, ..., xn]\<close> (a boxed slice turned into a vector): the capacity is \<open>n\<close>.\<close>
definition rvec_from_list_val :: \<open>elem_layout \<Rightarrow> 'v list \<Rightarrow> 'v rvec\<close> where
  \<open>rvec_from_list_val l xs \<equiv> rvec_make l xs (length xs)\<close>

text\<open>\<^verbatim>\<open>Clone::clone\<close> (\<^verbatim>\<open><[T]>::to_vec\<close>): a new allocation for the elements, whose
  elements are the clones (here: the same values).\<close>
definition rvec_clone_val :: \<open>'v rvec \<Rightarrow> 'v rvec\<close> where
  \<open>rvec_clone_val v \<equiv> rvec_make (rvec_layout v) (rvec_elems v) (rvec_alloc_cap (rvec_layout v) (rvec_length v))\<close>

text\<open>\<^verbatim>\<open>Vec::reserve(n)\<close>: room for \<open>n\<close> more elements, by amortised growth.\<close>
definition rvec_reserve_val :: \<open>'v rvec \<Rightarrow> nat \<Rightarrow> 'v rvec option\<close> where
  \<open>rvec_reserve_val v n \<equiv>
     if n \<le> rvec_cap v - rvec_length v then Some v
     else let m = rvec_grow_cap (rvec_layout v) (rvec_cap v) (rvec_length v + n) in
       if m \<le> rvec_cap_max (rvec_layout v) then Some (update_rvec_cap (\<lambda>_. m) v) else None\<close>

text\<open>\<^verbatim>\<open>Vec::reserve_exact(n)\<close>: room for \<open>n\<close> more elements, by a new allocation.\<close>
definition rvec_reserve_exact_val :: \<open>'v rvec \<Rightarrow> nat \<Rightarrow> 'v rvec option\<close> where
  \<open>rvec_reserve_exact_val v n \<equiv>
     if n \<le> rvec_cap v - rvec_length v then Some v
     else if rvec_length v + n \<le> rvec_cap_max (rvec_layout v)
       then Some (update_rvec_cap (\<lambda>_. rvec_alloc_cap (rvec_layout v) (rvec_length v + n)) v)
     else None\<close>

text\<open>Appending \<open>xs\<close> after \<^verbatim>\<open>reserve(len xs)\<close> (\<^verbatim>\<open>extend_from_slice\<close>; \<^verbatim>\<open>push\<close> is
  \<open>xs = [x]\<close>, which grows by one as \<^verbatim>\<open>grow_one\<close> does).\<close>
definition rvec_append_val :: \<open>'v rvec \<Rightarrow> 'v list \<Rightarrow> 'v rvec option\<close> where
  \<open>rvec_append_val v xs \<equiv> map_option (update_rvec_elems (\<lambda>ys. ys @ xs)) (rvec_reserve_val v (length xs))\<close>

text\<open>\<^verbatim>\<open>Vec::insert(i, x)\<close> for \<open>i \<le> len\<close>: grows by one if full.\<close>
definition rvec_insert_val :: \<open>'v rvec \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'v rvec option\<close> where
  \<open>rvec_insert_val v i x \<equiv>
     map_option (update_rvec_elems (\<lambda>ys. take i ys @ x # drop i ys)) (rvec_reserve_val v 1)\<close>

text\<open>\<^verbatim>\<open>Vec::resize(n, x)\<close>: truncates, or appends copies of \<open>x\<close>.\<close>
definition rvec_resize_val :: \<open>'v rvec \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 'v rvec option\<close> where
  \<open>rvec_resize_val v n x \<equiv>
     if n \<le> rvec_length v then Some (update_rvec_elems (take n) v)
     else rvec_append_val v (replicate (n - rvec_length v) x)\<close>

text\<open>\<^verbatim>\<open>Vec::shrink_to(n)\<close>; \<^verbatim>\<open>shrink_to_fit\<close> is \<open>n = 0\<close>. A vector of zero-sized
  elements keeps its capacity.\<close>
definition rvec_shrink_to_val :: \<open>'v rvec \<Rightarrow> nat \<Rightarrow> 'v rvec\<close> where
  \<open>rvec_shrink_to_val v n \<equiv>
     if layout_size (rvec_layout v) \<noteq> 0 \<and> max (rvec_length v) n < rvec_cap v
       then update_rvec_cap (\<lambda>c. rvec_shrink_cap (rvec_layout v) c (max (rvec_length v) n)) v
     else v\<close>

subsection\<open>The operations keep the invariant\<close>

text\<open>An operation that keeps the capacity and does not lengthen the vector keeps the invariant
  (\<^verbatim>\<open>pop\<close>, \<^verbatim>\<open>truncate\<close>, \<^verbatim>\<open>clear\<close>, \<^verbatim>\<open>remove\<close>, \<^verbatim>\<open>swap_remove\<close>, \<^verbatim>\<open>dedup\<close>, and
  every update of the elements through a slice, which keeps the length).\<close>
lemma rvec_wf_update_elems:
  assumes \<open>rvec_wf v\<close> and \<open>length (f (rvec_elems v)) \<le> rvec_length v\<close>
  shows \<open>rvec_wf (update_rvec_elems f v)\<close>
  using assms by (auto simp add: rvec_wf_def)

lemma rvec_new_val_wf:
  shows \<open>rvec_wf (rvec_new_val l)\<close>
  by (simp add: rvec_new_val_def rvec_make_wf)

lemma rvec_new_val_components [simp]:
  shows \<open>rvec_elems (rvec_new_val l) = []\<close> and \<open>rvec_layout (rvec_new_val l) = l\<close>
  by (simp_all add: rvec_new_val_def)

lemma rvec_with_capacity_val_Some:
  assumes \<open>rvec_with_capacity_val l n = Some v\<close>
  shows \<open>rvec_wf v\<close> and \<open>rvec_elems v = []\<close> and \<open>rvec_layout v = l\<close> and \<open>n \<le> rvec_cap v\<close>
  using assms rvec_alloc_cap_bounds[of n l]
  by (auto simp add: rvec_with_capacity_val_def rvec_make_wf rvec_cap_max_def split: if_splits)

lemma rvec_with_capacity_val_None_iff:
  shows \<open>rvec_with_capacity_val l n = None \<longleftrightarrow> rvec_cap_max l < n\<close>
  by (auto simp add: rvec_with_capacity_val_def)

lemma rvec_from_elem_val_Some:
  assumes \<open>rvec_from_elem_val l x n = Some v\<close>
  shows \<open>rvec_wf v\<close> and \<open>rvec_elems v = replicate n x\<close> and \<open>rvec_layout v = l\<close>
  using assms rvec_alloc_cap_bounds[of n l]
  by (auto simp add: rvec_from_elem_val_def rvec_make_wf split: if_splits)

lemma rvec_from_elem_val_None_iff:
  shows \<open>rvec_from_elem_val l x n = None \<longleftrightarrow> rvec_cap_max l < n\<close>
  by (auto simp add: rvec_from_elem_val_def)

lemma rvec_from_list_val_wf:
  assumes \<open>length xs \<le> rvec_cap_max l\<close>
  shows \<open>rvec_wf (rvec_from_list_val l xs)\<close>
  using assms by (simp add: rvec_from_list_val_def rvec_make_wf)

lemma rvec_clone_val:
  assumes \<open>rvec_wf v\<close>
  shows \<open>rvec_wf (rvec_clone_val v)\<close> and \<open>rvec_elems (rvec_clone_val v) = rvec_elems v\<close>
    and \<open>rvec_layout (rvec_clone_val v) = rvec_layout v\<close>
  using assms rvec_alloc_cap_bounds[of \<open>rvec_length v\<close> \<open>rvec_layout v\<close>]
  by (auto simp add: rvec_clone_val_def rvec_wf_def intro!: rvec_make_wf)

lemma rvec_reserve_val_Some:
  assumes \<open>rvec_reserve_val v n = Some w\<close> and \<open>rvec_wf v\<close>
  shows \<open>rvec_wf w\<close> and \<open>rvec_elems w = rvec_elems v\<close> and \<open>rvec_layout w = rvec_layout v\<close>
    and \<open>rvec_length v + n \<le> rvec_cap w\<close> and \<open>rvec_cap v \<le> rvec_cap w\<close>
  using assms rvec_grow_cap_bounds[where n=\<open>rvec_length v + n\<close> and l=\<open>rvec_layout v\<close> and c=\<open>rvec_cap v\<close>]
    rvec_cap_max_le_usize_max[of \<open>rvec_layout v\<close>]
  by (auto simp add: rvec_reserve_val_def rvec_wf_def Let_def split: if_splits)

text\<open>A sufficient condition for \<^verbatim>\<open>reserve\<close> not to panic: the growth cannot exceed the bound.\<close>
lemma rvec_reserve_val_not_None:
  assumes \<open>rvec_wf v\<close>
      and \<open>rvec_length v + n \<le> rvec_cap v \<or>
           max (2 * rvec_cap v) (max (rvec_length v + n) (rvec_min_non_zero_cap (rvec_layout v)))
             \<le> rvec_cap_max (rvec_layout v)\<close>
  shows \<open>rvec_reserve_val v n \<noteq> None\<close>
  using assms rvec_grow_cap_bounds[where n=\<open>rvec_length v + n\<close> and l=\<open>rvec_layout v\<close> and c=\<open>rvec_cap v\<close>]
  by (auto simp add: rvec_reserve_val_def rvec_wf_def Let_def)

lemma rvec_reserve_val_None_if:
  assumes \<open>rvec_wf v\<close> and \<open>rvec_cap_max (rvec_layout v) < rvec_length v + n\<close>
  shows \<open>rvec_reserve_val v n = None\<close>
  using assms rvec_grow_cap_bounds[where n=\<open>rvec_length v + n\<close> and l=\<open>rvec_layout v\<close> and c=\<open>rvec_cap v\<close>]
  by (auto simp add: rvec_reserve_val_def rvec_wf_def Let_def)

lemma rvec_reserve_exact_val_Some:
  assumes \<open>rvec_reserve_exact_val v n = Some w\<close> and \<open>rvec_wf v\<close>
  shows \<open>rvec_wf w\<close> and \<open>rvec_elems w = rvec_elems v\<close> and \<open>rvec_layout w = rvec_layout v\<close>
    and \<open>rvec_length v + n \<le> rvec_cap w\<close> and \<open>rvec_cap v \<le> rvec_cap w\<close>
  using assms rvec_alloc_cap_bounds[where n=\<open>rvec_length v + n\<close> and l=\<open>rvec_layout v\<close>]
    rvec_cap_max_le_usize_max[of \<open>rvec_layout v\<close>]
  by (auto simp add: rvec_reserve_exact_val_def rvec_wf_def split: if_splits)

lemma rvec_reserve_exact_val_None_iff:
  assumes \<open>rvec_wf v\<close>
  shows \<open>rvec_reserve_exact_val v n = None \<longleftrightarrow> rvec_cap_max (rvec_layout v) < rvec_length v + n\<close>
  using assms by (auto simp add: rvec_reserve_exact_val_def rvec_wf_def)

lemma rvec_append_val_Some:
  assumes \<open>rvec_append_val v xs = Some w\<close> and \<open>rvec_wf v\<close>
  shows \<open>rvec_wf w\<close> and \<open>rvec_elems w = rvec_elems v @ xs\<close> and \<open>rvec_layout w = rvec_layout v\<close>
    and \<open>rvec_cap v \<le> rvec_cap w\<close>
proof -
  obtain u where u: \<open>rvec_reserve_val v (length xs) = Some u\<close>
      and w: \<open>w = update_rvec_elems (\<lambda>ys. ys @ xs) u\<close>
    using assms(1) by (auto simp add: rvec_append_val_def)
  show \<open>rvec_wf w\<close> and \<open>rvec_elems w = rvec_elems v @ xs\<close> and \<open>rvec_layout w = rvec_layout v\<close>
    and \<open>rvec_cap v \<le> rvec_cap w\<close>
    using rvec_reserve_val_Some[OF u assms(2)] w by (auto simp add: rvec_wf_def)
qed

text\<open>Appending within the capacity does not change the capacity.\<close>
lemma rvec_append_val_within_cap:
  assumes \<open>rvec_length v + length xs \<le> rvec_cap v\<close>
  shows \<open>rvec_append_val v xs = Some (update_rvec_elems (\<lambda>ys. ys @ xs) v)\<close>
  using assms by (auto simp add: rvec_append_val_def rvec_reserve_val_def)

lemma rvec_append_val_None_iff:
  shows \<open>rvec_append_val v xs = None \<longleftrightarrow> rvec_reserve_val v (length xs) = None\<close>
  by (simp add: rvec_append_val_def)

lemma rvec_insert_val_Some:
  assumes \<open>rvec_insert_val v i x = Some w\<close> and \<open>rvec_wf v\<close>
  shows \<open>rvec_wf w\<close> and \<open>rvec_elems w = take i (rvec_elems v) @ x # drop i (rvec_elems v)\<close>
    and \<open>rvec_layout w = rvec_layout v\<close>
proof -
  obtain u where u: \<open>rvec_reserve_val v 1 = Some u\<close>
      and w: \<open>w = update_rvec_elems (\<lambda>ys. take i ys @ x # drop i ys) u\<close>
    using assms(1) by (auto simp add: rvec_insert_val_def)
  show \<open>rvec_wf w\<close> and \<open>rvec_elems w = take i (rvec_elems v) @ x # drop i (rvec_elems v)\<close>
    and \<open>rvec_layout w = rvec_layout v\<close>
    using rvec_reserve_val_Some[OF u assms(2)] w by (auto simp add: rvec_wf_def)
qed

lemma rvec_resize_val_Some:
  assumes \<open>rvec_resize_val v n x = Some w\<close> and \<open>rvec_wf v\<close>
  shows \<open>rvec_wf w\<close> and \<open>rvec_elems w = take n (rvec_elems v) @ replicate (n - rvec_length v) x\<close>
    and \<open>rvec_layout w = rvec_layout v\<close>
  using assms rvec_append_val_Some[of v \<open>replicate (n - rvec_length v) x\<close> w]
    rvec_wf_update_elems[of v \<open>take n\<close>]
  by (auto simp add: rvec_resize_val_def split: if_splits)

lemma rvec_shrink_to_val:
  assumes \<open>rvec_wf v\<close>
  shows \<open>rvec_wf (rvec_shrink_to_val v n)\<close> and \<open>rvec_elems (rvec_shrink_to_val v n) = rvec_elems v\<close>
    and \<open>rvec_layout (rvec_shrink_to_val v n) = rvec_layout v\<close>
    and \<open>rvec_cap (rvec_shrink_to_val v n) \<le> rvec_cap v\<close>
  using assms rvec_shrink_cap_bounds[where c=\<open>rvec_cap v\<close> and n=\<open>max (rvec_length v) n\<close> and l=\<open>rvec_layout v\<close>]
  by (auto simp add: rvec_shrink_to_val_def rvec_wf_def)

subsection\<open>The focus on the elements\<close>

text\<open>\<^verbatim>\<open>Deref\<close>/\<^verbatim>\<open>DerefMut\<close> to the slice \<^verbatim>\<open>[T]\<close>. An update through it may change the
  length; a mutable slice keeps it, and then the vector keeps its invariant
  (@{thm [source] rvec_wf_update_elems}).\<close>
lift_definition rvec_elems_focus :: \<open>('v rvec, 'v list) focus\<close> is
  \<open>make_focus_raw_via_view_modify (\<lambda>v. Some (rvec_elems v)) update_rvec_elems\<close>
  by (intro is_valid_focus_via_modifyI) (auto simp add: is_valid_view_modify_def rvec.expand)

lemma rvec_elems_focus_components [focus_components]:
  shows \<open>focus_view rvec_elems_focus = (\<lambda>v. Some (rvec_elems v))\<close>
    and \<open>focus_update rvec_elems_focus y v = update_rvec_elems (\<lambda>_. y) v\<close>
  by (transfer; simp add: make_focus_raw_via_view_modify_def)+

subsection\<open>Models of the functions\<close>

text\<open>The functions that take a vector by value or by shared reference (the frontend passes
  \<^verbatim>\<open>&Vec<T>\<close> as the value).\<close>

definition rvec_new :: \<open>elem_layout \<Rightarrow> ('s, 'v rvec, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_new l \<equiv> FunctionBody (literal (rvec_new_val l))\<close>

definition rvec_new_contract :: \<open>elem_layout \<Rightarrow> ('s::sepalg, 'v rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>rvec_new_contract l \<equiv>
     let pre = emp in
     let post = \<lambda>r. \<langle>r = rvec_new_val l\<rangle> in
       make_function_contract pre post\<close>

lemma rvec_new_spec [crush_specs]:
  shows \<open>\<Gamma> ; rvec_new l \<Turnstile>\<^sub>F rvec_new_contract l\<close>
  by (crush_boot f: rvec_new_def contract: rvec_new_contract_def) crush_base

text\<open>\<^verbatim>\<open>Vec::with_capacity(n)\<close>.\<close>
definition rvec_with_capacity :: \<open>elem_layout \<Rightarrow> 64 word \<Rightarrow> ('s, 'v rvec, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_with_capacity l n \<equiv> FunctionBody \<lbrakk>
     match \<llangle>rvec_with_capacity_val l (unat n)\<rrangle> {
       Some(v) \<Rightarrow> v,
       None \<Rightarrow> panic!("capacity overflow")
     }
  \<rbrakk>\<close>

definition rvec_with_capacity_contract :: \<open>elem_layout \<Rightarrow> 64 word \<Rightarrow> ('s::sepalg, 'v rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>rvec_with_capacity_contract l n \<equiv>
     let pre = \<langle>unat n \<le> rvec_cap_max l\<rangle> in
     let post = \<lambda>r. \<langle>rvec_with_capacity_val l (unat n) = Some r\<rangle> in
       make_function_contract pre post\<close>

lemma rvec_with_capacity_spec [crush_specs]:
  shows \<open>\<Gamma> ; rvec_with_capacity l n \<Turnstile>\<^sub>F rvec_with_capacity_contract l n\<close>
  by (crush_boot f: rvec_with_capacity_def contract: rvec_with_capacity_contract_def)
     (crush_base simp add: rvec_with_capacity_val_def)

text\<open>\<^verbatim>\<open>vec![x; n]\<close>.\<close>
definition rvec_from_elem :: \<open>elem_layout \<Rightarrow> 'v \<Rightarrow> 64 word \<Rightarrow> ('s, 'v rvec, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_from_elem l x n \<equiv> FunctionBody \<lbrakk>
     match \<llangle>rvec_from_elem_val l x (unat n)\<rrangle> {
       Some(v) \<Rightarrow> v,
       None \<Rightarrow> panic!("capacity overflow")
     }
  \<rbrakk>\<close>

definition rvec_from_elem_contract :: \<open>elem_layout \<Rightarrow> 'v \<Rightarrow> 64 word \<Rightarrow> ('s::sepalg, 'v rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>rvec_from_elem_contract l x n \<equiv>
     let pre = \<langle>unat n \<le> rvec_cap_max l\<rangle> in
     let post = \<lambda>r. \<langle>rvec_from_elem_val l x (unat n) = Some r\<rangle> in
       make_function_contract pre post\<close>

lemma rvec_from_elem_spec [crush_specs]:
  shows \<open>\<Gamma> ; rvec_from_elem l x n \<Turnstile>\<^sub>F rvec_from_elem_contract l x n\<close>
  by (crush_boot f: rvec_from_elem_def contract: rvec_from_elem_contract_def)
     (crush_base simp add: rvec_from_elem_val_def)

text\<open>\<^verbatim>\<open>vec![x1, ..., xn]\<close>.\<close>
definition rvec_from_list :: \<open>elem_layout \<Rightarrow> 'v list \<Rightarrow> ('s, 'v rvec, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_from_list l xs \<equiv> FunctionBody (literal (rvec_from_list_val l xs))\<close>

text\<open>\<^verbatim>\<open>Clone::clone\<close>.\<close>
definition rvec_clone :: \<open>'v rvec \<Rightarrow> ('s, 'v rvec, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_clone v \<equiv> FunctionBody (literal (rvec_clone_val v))\<close>

text\<open>\<^verbatim>\<open>Vec::len\<close>, \<^verbatim>\<open>Vec::capacity\<close>, \<^verbatim>\<open>Vec::is_empty\<close>, and the elements as a slice
  (\<^verbatim>\<open>as_slice\<close>, \<^verbatim>\<open>Deref\<close>).\<close>
definition rvec_len :: \<open>'v rvec \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_len v \<equiv> FunctionBody (literal (of_nat (rvec_length v)))\<close>

definition rvec_capacity :: \<open>'v rvec \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_capacity v \<equiv> FunctionBody (literal (of_nat (rvec_cap v)))\<close>

definition rvec_is_empty :: \<open>'v rvec \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_is_empty v \<equiv> FunctionBody (literal (rvec_elems v = []))\<close>

definition rvec_as_slice :: \<open>'v rvec \<Rightarrow> ('s, 'v list, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_as_slice v \<equiv> FunctionBody (literal (rvec_elems v))\<close>

definition rvec_value_contract :: \<open>'r \<Rightarrow> ('s::sepalg, 'r, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>rvec_value_contract x \<equiv>
     let pre = emp in
     let post = \<lambda>r. \<langle>r = x\<rangle> in
       make_function_contract pre post\<close>

lemma rvec_value_specs [crush_specs]:
  shows \<open>\<Gamma> ; rvec_from_list l xs \<Turnstile>\<^sub>F rvec_value_contract (rvec_from_list_val l xs)\<close>
    and \<open>\<Gamma> ; rvec_clone v \<Turnstile>\<^sub>F rvec_value_contract (rvec_clone_val v)\<close>
    and \<open>\<Gamma> ; rvec_len v \<Turnstile>\<^sub>F rvec_value_contract (of_nat (rvec_length v))\<close>
    and \<open>\<Gamma> ; rvec_capacity v \<Turnstile>\<^sub>F rvec_value_contract (of_nat (rvec_cap v))\<close>
    and \<open>\<Gamma> ; rvec_is_empty v \<Turnstile>\<^sub>F rvec_value_contract (rvec_elems v = [])\<close>
    and \<open>\<Gamma> ; rvec_as_slice v \<Turnstile>\<^sub>F rvec_value_contract (rvec_elems v)\<close>
  subgoal by (crush_boot f: rvec_from_list_def contract: rvec_value_contract_def) crush_base
  subgoal by (crush_boot f: rvec_clone_def contract: rvec_value_contract_def) crush_base
  subgoal by (crush_boot f: rvec_len_def contract: rvec_value_contract_def) crush_base
  subgoal by (crush_boot f: rvec_capacity_def contract: rvec_value_contract_def) crush_base
  subgoal by (crush_boot f: rvec_is_empty_def contract: rvec_value_contract_def) crush_base
  subgoal by (crush_boot f: rvec_as_slice_def contract: rvec_value_contract_def) crush_base
  done

text\<open>On a well-formed vector, \<^verbatim>\<open>len\<close> and \<^verbatim>\<open>capacity\<close> do not wrap around.\<close>
lemma rvec_len_unat:
  assumes \<open>rvec_wf v\<close>
  shows \<open>unat (of_nat (rvec_length v) :: 64 word) = rvec_length v\<close>
    and \<open>unat (of_nat (rvec_cap v) :: 64 word) = rvec_cap v\<close>
  using rvec_wf_length_bound[OF assms] by (simp_all add: unat_of_nat_eq)

subsection\<open>Conversions and comparisons\<close>

text\<open>The layout of an element type that is a type parameter. The translation of generic code
  does not know it: it is an unspecified constant for each HOL type (also the same for Rust types
  of the same HOL type, such as \<^verbatim>\<open>T\<close> and \<^verbatim>\<open>&T\<close>), so a proof can use no property of it.\<close>
consts rvec_layout_of :: \<open>'a itself \<Rightarrow> elem_layout\<close>

text\<open>A new vector of the elements \<open>xs\<close>, with a capacity of at least their number
  (\<^verbatim>\<open><[T]>::to_vec\<close>, \<^verbatim>\<open>collect\<close>, \<^verbatim>\<open>From<&[T]>\<close>, and \<^verbatim>\<open>String::into_bytes\<close>, whose
  capacity is the string's, which the model of strings does not have); panics if there are too
  many elements.\<close>
definition rvec_alloc_val :: \<open>elem_layout \<Rightarrow> 'v list \<Rightarrow> 'v rvec option\<close> where
  \<open>rvec_alloc_val l xs \<equiv>
     if length xs \<le> rvec_cap_max l then Some (rvec_make l xs (rvec_alloc_cap l (length xs))) else None\<close>

lemma rvec_alloc_val_Some:
  assumes \<open>rvec_alloc_val l xs = Some v\<close>
  shows \<open>rvec_wf v\<close> and \<open>rvec_elems v = xs\<close> and \<open>rvec_layout v = l\<close>
  using assms rvec_alloc_cap_bounds[of \<open>length xs\<close> l]
  by (auto simp add: rvec_alloc_val_def rvec_make_wf split: if_splits)

definition rvec_of_list_alloc :: \<open>elem_layout \<Rightarrow> 'v list \<Rightarrow> ('s, 'v rvec, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_of_list_alloc l xs \<equiv> FunctionBody \<lbrakk>
     match \<llangle>rvec_alloc_val l xs\<rrangle> {
       Some(v) \<Rightarrow> v,
       None \<Rightarrow> panic!("capacity overflow")
     }
  \<rbrakk>\<close>

definition rvec_of_list_alloc_contract :: \<open>elem_layout \<Rightarrow> 'v list \<Rightarrow> ('s::sepalg, 'v rvec, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>rvec_of_list_alloc_contract l xs \<equiv>
     let pre = \<langle>length xs \<le> rvec_cap_max l\<rangle> in
     let post = \<lambda>r. \<langle>rvec_alloc_val l xs = Some r\<rangle> in
       make_function_contract pre post\<close>

lemma rvec_of_list_alloc_spec [crush_specs]:
  shows \<open>\<Gamma> ; rvec_of_list_alloc l xs \<Turnstile>\<^sub>F rvec_of_list_alloc_contract l xs\<close>
  by (crush_boot f: rvec_of_list_alloc_def contract: rvec_of_list_alloc_contract_def)
     (crush_base simp add: rvec_alloc_val_def)

text\<open>\<^verbatim>\<open>PartialEq\<close> of vectors whose elements' \<^verbatim>\<open>PartialEq\<close> is HOL's equality: the elements
  (not the capacities) are compared.\<close>
definition rvec_eq :: \<open>'v rvec \<Rightarrow> 'v rvec \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_eq a b \<equiv> FunctionBody (literal (rvec_elems a = rvec_elems b))\<close>

definition rvec_ne :: \<open>'v rvec \<Rightarrow> 'v rvec \<Rightarrow> ('s, bool, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_ne a b \<equiv> FunctionBody (literal (rvec_elems a \<noteq> rvec_elems b))\<close>

text\<open>\<^verbatim>\<open>TryFrom<Vec<T>>\<close> for \<^verbatim>\<open>[T; N]\<close> (and \<^verbatim>\<open>Box<[T; N]>\<close>): \<^verbatim>\<open>Ok\<close> iff the vector has
  \<open>N\<close> elements, otherwise the vector is the error.\<close>
definition rvec_try_into_array :: \<open>'v rvec \<Rightarrow> 64 word \<Rightarrow> ('s, ('v list, 'v rvec) result, 'abort, 'i, 'o) function_body\<close> where
  \<open>rvec_try_into_array v n \<equiv> FunctionBody (literal (if rvec_length v = unat n then Ok (rvec_elems v) else Err v))\<close>

lemma rvec_compare_specs [crush_specs]:
  shows \<open>\<Gamma> ; rvec_eq a b \<Turnstile>\<^sub>F rvec_value_contract (rvec_elems a = rvec_elems b)\<close>
    and \<open>\<Gamma> ; rvec_ne a b \<Turnstile>\<^sub>F rvec_value_contract (rvec_elems a \<noteq> rvec_elems b)\<close>
    and \<open>\<Gamma> ; rvec_try_into_array v n \<Turnstile>\<^sub>F
           rvec_value_contract (if rvec_length v = unat n then Ok (rvec_elems v) else Err v)\<close>
  subgoal by (crush_boot f: rvec_eq_def contract: rvec_value_contract_def) crush_base
  subgoal by (crush_boot f: rvec_ne_def contract: rvec_value_contract_def) crush_base
  subgoal by (crush_boot f: rvec_try_into_array_def contract: rvec_value_contract_def) crush_base
  done

text\<open>The functions that take a vector by mutable reference.\<close>

context reference
begin

adhoc_overloading store_update_const \<rightleftharpoons> update_fun

text\<open>\<^verbatim>\<open>Vec::as_mut_slice\<close>, \<^verbatim>\<open>DerefMut\<close>: the reference to the elements.\<close>
definition rvec_as_mut_slice :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow>
      ('s, ('a, 'b, 'v list) Global_Store.ref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_as_mut_slice ptr \<equiv> FunctionBody (literal (focus_focused rvec_elems_focus ptr))\<close>

definition rvec_as_mut_slice_contract where
  [crush_contracts]: \<open>rvec_as_mut_slice_contract (ptr :: ('a, 'b, 'v rvec) Global_Store.ref) \<equiv>
     let pre = emp in
     let post = \<lambda>r. \<langle>r = focus_focused rvec_elems_focus ptr\<rangle> in
       make_function_contract pre post\<close>

lemma rvec_as_mut_slice_spec [crush_specs]:
  shows \<open>\<Gamma> ; rvec_as_mut_slice ptr \<Turnstile>\<^sub>F rvec_as_mut_slice_contract ptr\<close>
  by (crush_boot f: rvec_as_mut_slice_def contract: rvec_as_mut_slice_contract_def) crush_base

text\<open>An update of the vector that panics with \<^verbatim>\<open>capacity overflow\<close> when \<open>f\<close> gives
  \<^term>\<open>None\<close>.\<close>
definition rvec_update_or_overflow :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> ('v rvec \<Rightarrow> 'v rvec option) \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_update_or_overflow ptr f \<equiv> FunctionBody \<lbrakk>
     let v = *ptr;
     match \<llangle>f v\<rrangle> {
       Some(w) \<Rightarrow> {
         ptr = w;
         ()
       },
       None \<Rightarrow> panic!("capacity overflow")
     }
  \<rbrakk>\<close>

definition rvec_update_or_overflow_contract where
  [crush_contracts]: \<open>rvec_update_or_overflow_contract (ptr :: ('a, 'b, 'v rvec) Global_Store.ref) g v f \<equiv>
     let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>f v \<noteq> None\<rangle> in
     let post = \<lambda>_. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. the (f v)) \<sqdot> (g\<down>v) in
       make_function_contract pre post\<close>

lemma rvec_update_or_overflow_spec [crush_specs]:
  shows \<open>\<Gamma> ; rvec_update_or_overflow ptr f \<Turnstile>\<^sub>F rvec_update_or_overflow_contract ptr g v f\<close>
  by (crush_boot f: rvec_update_or_overflow_def contract: rvec_update_or_overflow_contract_def) crush_base

text\<open>\<^verbatim>\<open>Vec::push\<close>, \<^verbatim>\<open>extend_from_slice\<close>, \<^verbatim>\<open>reserve\<close>, \<^verbatim>\<open>reserve_exact\<close>,
  \<^verbatim>\<open>resize\<close>. Their contracts are those of @{const rvec_update_or_overflow}.\<close>
definition rvec_push :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_push ptr x \<equiv> rvec_update_or_overflow ptr (\<lambda>v. rvec_append_val v [x])\<close>

definition rvec_extend_from_slice :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 'v list \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_extend_from_slice ptr xs \<equiv> rvec_update_or_overflow ptr (\<lambda>v. rvec_append_val v xs)\<close>

definition rvec_reserve :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_reserve ptr n \<equiv> rvec_update_or_overflow ptr (\<lambda>v. rvec_reserve_val v (unat n))\<close>

definition rvec_reserve_exact :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_reserve_exact ptr n \<equiv> rvec_update_or_overflow ptr (\<lambda>v. rvec_reserve_exact_val v (unat n))\<close>

definition rvec_resize :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow> 'v \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_resize ptr n x \<equiv> rvec_update_or_overflow ptr (\<lambda>v. rvec_resize_val v (unat n) x)\<close>

lemma rvec_grow_specs [crush_specs]:
  shows \<open>\<Gamma> ; rvec_push ptr x \<Turnstile>\<^sub>F rvec_update_or_overflow_contract ptr g v (\<lambda>v. rvec_append_val v [x])\<close>
    and \<open>\<Gamma> ; rvec_extend_from_slice ptr xs \<Turnstile>\<^sub>F rvec_update_or_overflow_contract ptr g v (\<lambda>v. rvec_append_val v xs)\<close>
    and \<open>\<Gamma> ; rvec_reserve ptr n \<Turnstile>\<^sub>F rvec_update_or_overflow_contract ptr g v (\<lambda>v. rvec_reserve_val v (unat n))\<close>
    and \<open>\<Gamma> ; rvec_reserve_exact ptr n \<Turnstile>\<^sub>F rvec_update_or_overflow_contract ptr g v (\<lambda>v. rvec_reserve_exact_val v (unat n))\<close>
    and \<open>\<Gamma> ; rvec_resize ptr n x \<Turnstile>\<^sub>F rvec_update_or_overflow_contract ptr g v (\<lambda>v. rvec_resize_val v (unat n) x)\<close>
  by (simp_all only: rvec_push_def rvec_extend_from_slice_def rvec_reserve_def rvec_reserve_exact_def
      rvec_resize_def rvec_update_or_overflow_spec)

text\<open>\<^verbatim>\<open>Vec::insert(i, x)\<close>: panics if \<open>i > len\<close>, then grows by one if full.\<close>
definition rvec_insert :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow> 'v \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_insert ptr i x \<equiv> FunctionBody \<lbrakk>
     let v = *ptr;
     if \<llangle>rvec_length v < unat i\<rrangle> {
       panic!("insertion index should be <= len")
     };
     match \<llangle>rvec_insert_val v (unat i) x\<rrangle> {
       Some(w) \<Rightarrow> {
         ptr = w;
         ()
       },
       None \<Rightarrow> panic!("capacity overflow")
     }
  \<rbrakk>\<close>

definition rvec_insert_contract where
  [crush_contracts]: \<open>rvec_insert_contract (ptr :: ('a, 'b, 'v rvec) Global_Store.ref) g v i x \<equiv>
     let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>unat i \<le> rvec_length v \<and> rvec_insert_val v (unat i) x \<noteq> None\<rangle> in
     let post = \<lambda>_. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. the (rvec_insert_val v (unat i) x)) \<sqdot> (g\<down>v) in
       make_function_contract pre post\<close>

lemma rvec_insert_spec [crush_specs]:
  shows \<open>\<Gamma> ; rvec_insert ptr i x \<Turnstile>\<^sub>F rvec_insert_contract ptr g v i x\<close>
  by (crush_boot f: rvec_insert_def contract: rvec_insert_contract_def) crush_base

text\<open>The updates that cannot panic.\<close>
definition rvec_update :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> ('v rvec \<Rightarrow> 'v rvec) \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_update ptr f \<equiv> FunctionBody \<lbrakk>
     let v = *ptr;
     ptr = \<llangle>f v\<rrangle>;
     ()
  \<rbrakk>\<close>

definition rvec_update_contract where
  [crush_contracts]: \<open>rvec_update_contract (ptr :: ('a, 'b, 'v rvec) Global_Store.ref) g v f \<equiv>
     let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v in
     let post = \<lambda>_. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. f v) \<sqdot> (g\<down>v) in
       make_function_contract pre post\<close>

lemma rvec_update_spec [crush_specs]:
  shows \<open>\<Gamma> ; rvec_update ptr f \<Turnstile>\<^sub>F rvec_update_contract ptr g v f\<close>
  by (crush_boot f: rvec_update_def contract: rvec_update_contract_def) crush_base

text\<open>\<^verbatim>\<open>Vec::truncate\<close>, \<^verbatim>\<open>clear\<close>, \<^verbatim>\<open>shrink_to\<close>, \<^verbatim>\<open>shrink_to_fit\<close>.\<close>
definition rvec_truncate :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_truncate ptr n \<equiv> rvec_update ptr (update_rvec_elems (take (unat n)))\<close>

definition rvec_clear :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_clear ptr \<equiv> rvec_update ptr (update_rvec_elems (\<lambda>_. []))\<close>

definition rvec_shrink_to :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_shrink_to ptr n \<equiv> rvec_update ptr (\<lambda>v. rvec_shrink_to_val v (unat n))\<close>

definition rvec_shrink_to_fit :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_shrink_to_fit ptr \<equiv> rvec_update ptr (\<lambda>v. rvec_shrink_to_val v 0)\<close>

text\<open>\<^verbatim>\<open>Vec::dedup\<close> (the elements' \<^verbatim>\<open>PartialEq\<close> is HOL's equality): removes the adjacent
  duplicates.\<close>
definition rvec_dedup :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_dedup ptr \<equiv> rvec_update ptr (update_rvec_elems remdups_adj)\<close>

lemma rvec_update_specs [crush_specs]:
  shows \<open>\<Gamma> ; rvec_truncate ptr n \<Turnstile>\<^sub>F rvec_update_contract ptr g v (update_rvec_elems (take (unat n)))\<close>
    and \<open>\<Gamma> ; rvec_clear ptr \<Turnstile>\<^sub>F rvec_update_contract ptr g v (update_rvec_elems (\<lambda>_. []))\<close>
    and \<open>\<Gamma> ; rvec_shrink_to ptr n \<Turnstile>\<^sub>F rvec_update_contract ptr g v (\<lambda>v. rvec_shrink_to_val v (unat n))\<close>
    and \<open>\<Gamma> ; rvec_shrink_to_fit ptr \<Turnstile>\<^sub>F rvec_update_contract ptr g v (\<lambda>v. rvec_shrink_to_val v 0)\<close>
    and \<open>\<Gamma> ; rvec_dedup ptr \<Turnstile>\<^sub>F rvec_update_contract ptr g v (update_rvec_elems remdups_adj)\<close>
  by (simp_all only: rvec_truncate_def rvec_clear_def rvec_shrink_to_def rvec_shrink_to_fit_def
      rvec_dedup_def rvec_update_spec)

text\<open>\<^verbatim>\<open>Vec::pop\<close>: the last element, \<^verbatim>\<open>None\<close> if empty.\<close>
definition rvec_pop :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow>
      ('s, 'v option, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_pop ptr \<equiv> FunctionBody \<lbrakk>
     let v = *ptr;
     if \<llangle>rvec_elems v = []\<rrangle> {
        return None;
     };
     ptr = \<llangle>update_rvec_elems butlast v\<rrangle>;
     \<llangle>Some (last (rvec_elems v))\<rrangle>
  \<rbrakk>\<close>

definition rvec_pop_contract where
  [crush_contracts]: \<open>rvec_pop_contract (ptr :: ('a, 'b, 'v rvec) Global_Store.ref) g v \<equiv>
     let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v in
     let post = \<lambda>r. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. update_rvec_elems butlast v) \<sqdot> (g\<down>v) \<star>
                    \<langle>r = (if rvec_elems v = [] then None else Some (last (rvec_elems v)))\<rangle> in
       make_function_contract pre post\<close>

lemma rvec_pop_spec [crush_specs]:
  shows \<open>\<Gamma> ; rvec_pop ptr \<Turnstile>\<^sub>F rvec_pop_contract ptr g v\<close>
  apply (crush_boot f: rvec_pop_def contract: rvec_pop_contract_def)
  apply crush_base
  apply (auto simp add: rvec.expand)
  done

text\<open>\<^verbatim>\<open>Vec::remove(i)\<close>: the \<open>i\<close>-th element, the later ones shift down; panics if out of
  bounds.\<close>
definition rvec_remove :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, 'v, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_remove ptr i \<equiv> FunctionBody \<lbrakk>
     let v = *ptr;
     if \<llangle>unat i < rvec_length v\<rrangle> {
        ptr = \<llangle>update_rvec_elems (\<lambda>xs. take (unat i) xs @ drop (Suc (unat i)) xs) v\<rrangle>;
        \<llangle>rvec_elems v ! unat i\<rrangle>
     } else {
        panic!("removal index should be < len")
     }
  \<rbrakk>\<close>

text\<open>\<^verbatim>\<open>Vec::swap_remove(i)\<close>: the \<open>i\<close>-th element, replaced by the last one; panics if out
  of bounds.\<close>
definition rvec_swap_remove :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 64 word \<Rightarrow>
      ('s, 'v, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_swap_remove ptr i \<equiv> FunctionBody \<lbrakk>
     let v = *ptr;
     if \<llangle>unat i < rvec_length v\<rrangle> {
        ptr = \<llangle>update_rvec_elems (\<lambda>xs. butlast (xs[unat i := last xs])) v\<rrangle>;
        \<llangle>rvec_elems v ! unat i\<rrangle>
     } else {
        panic!("swap_remove index should be < len")
     }
  \<rbrakk>\<close>

definition rvec_remove_contract where
  [crush_contracts]: \<open>rvec_remove_contract (ptr :: ('a, 'b, 'v rvec) Global_Store.ref) g v i f \<equiv>
     let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>unat i < rvec_length v\<rangle> in
     let post = \<lambda>r. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. update_rvec_elems f v) \<sqdot> (g\<down>v) \<star>
                    \<langle>r = rvec_elems v ! unat i\<rangle> in
       make_function_contract pre post\<close>

lemma rvec_remove_specs [crush_specs]:
  shows \<open>\<Gamma> ; rvec_remove ptr i \<Turnstile>\<^sub>F
           rvec_remove_contract ptr g v i (\<lambda>xs. take (unat i) xs @ drop (Suc (unat i)) xs)\<close>
    and \<open>\<Gamma> ; rvec_swap_remove ptr i \<Turnstile>\<^sub>F
           rvec_remove_contract ptr g v i (\<lambda>xs. butlast (xs[unat i := last xs]))\<close>
  subgoal by (crush_boot f: rvec_remove_def contract: rvec_remove_contract_def) crush_base
  subgoal by (crush_boot f: rvec_swap_remove_def contract: rvec_remove_contract_def) crush_base
  done

subsection\<open>An example\<close>

text\<open>Two pushes within the capacity: the capacity is unchanged.\<close>
definition rvec_push_two_example :: \<open>('a, 'b, 'v rvec) Global_Store.ref \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow>
      ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>rvec_push_two_example ptr x y \<equiv> FunctionBody \<lbrakk>
     rvec_push(ptr, x);
     rvec_push(ptr, y)
  \<rbrakk>\<close>

definition rvec_push_two_example_contract where
  \<open>rvec_push_two_example_contract (ptr :: ('a, 'b, 'v rvec) Global_Store.ref) g v x y \<equiv>
     let pre = ptr \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>rvec_length v + 2 \<le> rvec_cap v\<rangle> in
     let post = \<lambda>_. ptr \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. update_rvec_elems (\<lambda>ys. ys @ [x, y]) v) \<sqdot> (g\<down>v) in
       make_function_contract pre post\<close>

lemma rvec_push_two_example_spec:
  shows \<open>\<Gamma> ; rvec_push_two_example ptr x y \<Turnstile>\<^sub>F rvec_push_two_example_contract ptr g v x y\<close>
  by (crush_boot f: rvec_push_two_example_def contract: rvec_push_two_example_contract_def)
     (crush_base simp add: rvec_append_val_within_cap)

no_adhoc_overloading store_update_const \<rightleftharpoons> update_fun

end

(*<*)
end
(*>*)
