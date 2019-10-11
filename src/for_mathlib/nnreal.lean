import data.real.nnreal
import analysis.complex.exponential

import valuation.linear_ordered_comm_group_with_zero

namespace nnreal

@[simp] lemma coe_max (x y : nnreal) : ((max x y : nnreal) : ℝ) = max (x : ℝ) (y : ℝ) :=
by { delta max, split_ifs; refl }

@[simp, move_cast] lemma coe_pow (x : nnreal) (n : ℕ) : ((x^n : nnreal) : ℝ) = x^n :=
by { induction n with n ih, { refl }, simp [nat.succ_eq_add_one, pow_add, ih], }

noncomputable instance : has_pow nnreal ℝ :=
{ pow := λ x q, ⟨x^q, real.rpow_nonneg_of_nonneg x.2 q⟩ }

variables (a b c : nnreal) (x y : ℝ)

lemma rpow_mul : a^(x * y) = (a^x)^y :=
subtype.coe_ext.mpr $ real.rpow_mul a.2 _ _

lemma mul_rpow : (a*b)^x = a^x * b^x :=
subtype.coe_ext.mpr $ real.mul_rpow a.2 b.2

@[elim_cast] lemma rpow_nat_cast (n : ℕ) : a^(n:ℝ) = a^n :=
subtype.coe_ext.mpr $ by exact_mod_cast real.rpow_nat_cast a n

@[simp] lemma rpow_one : a^(1:ℝ) = a :=
subtype.coe_ext.mpr $
by rw [← real.rpow_one a, ← nat.cast_one, rpow_nat_cast, real.rpow_nat_cast, coe_pow]

lemma rpow_le_rpow {a b : nnreal} (h : a ≤ b) (hx : 0 ≤ x) : a^x ≤ b^x :=
show (a^x : ℝ) ≤ b^x, from real.rpow_le_rpow a.2 h hx

open linear_ordered_structure

/-- The nonnegative real numbers form a linearly ordered commutative group with zero.-/
noncomputable instance : linear_ordered_comm_group_with_zero nnreal :=
{ inv_zero := by simp,
  zero_le' := zero_le,
  mul_le_mul_left := λ a b h c, mul_le_mul (le_refl _) h (zero_le _) (zero_le _),
  mul_inv_cancel := λ a h, mul_inv_cancel h,
  .. (infer_instance : zero_ne_one_class nnreal),
  .. (infer_instance : has_inv nnreal),
  .. (infer_instance : linear_order nnreal),
  .. (infer_instance : comm_semiring nnreal) }

--move this
lemma cardinal.eq_one_iff_nonempty_subsingleton {α : Type*} :
  cardinal.mk α = 1 ↔ (nonempty α ∧ subsingleton α) :=
begin
  symmetry,
  rw [← cardinal.ne_zero_iff_nonempty, ← cardinal.le_one_iff_subsingleton],
  rw [eq_iff_le_not_lt, ← cardinal.succ_zero, cardinal.lt_succ, cardinal.le_zero, and_comm],
end

-- move this
lemma exists_one_lt {α : Type*} [linear_ordered_comm_group α] (S : set α) [h : is_proper_convex S] :
  ∃ a : α, a ∈ S ∧ 1 < a :=
begin
  choose x y hx hy hxy using h.exists_ne,
  rcases lt_trichotomy 1 x with Hx|rfl|Hx,
  { use [x, hx, Hx] },
  { rcases lt_trichotomy 1 y with Hy|rfl|Hy,
    { use [y, hy, Hy] },
    { contradiction },
    { refine ⟨y⁻¹, is_convex.inv_mem hy, _⟩,
      simpa using mul_lt_right y⁻¹ Hy, } },
  { refine ⟨x⁻¹, is_convex.inv_mem hx, _⟩,
    simpa using mul_lt_right x⁻¹ Hx, }
end

-- move this
lemma exists_lt_one {α : Type*} [linear_ordered_comm_group α] (S : set α) [h : is_proper_convex S] :
  ∃ a : α, a ∈ S ∧ a < 1 :=
begin
  rcases exists_one_lt S with ⟨x, H1, H2⟩,
  use [x⁻¹, is_convex.inv_mem H1],
  simpa using mul_lt_right x⁻¹ H2,
end

open_locale classical

-- move this
lemma is_convex.mem_of_between' {α : Type*} [linear_ordered_comm_group α]
  (S : set α) [h : is_proper_convex S]
  {a b c : α} (ha : a ∈ S) (hc : c ∈ S) (hab : a ≤ b) (hbc : b ≤ c) :
  b ∈ S :=
begin
  cases le_total b 1 with hb hb,
  { exact is_convex.mem_of_between hab hb ha },
  rw ← _root_.inv_inv b,
  apply is_convex.inv_mem,
  apply @is_convex.mem_of_between α _ S _ c⁻¹ _ _ _ (is_convex.inv_mem hc),
  { contrapose! hbc, have := mul_lt_right (b*c) hbc,
    rwa [inv_mul_cancel_left, mul_left_comm, mul_left_inv, mul_one] at this },
  { contrapose! hb, simpa using mul_lt_right b hb, }
end

-- move this
lemma is_convex.pow_mem {α : Type*} [linear_ordered_comm_group α]
  (S : set α) [h : is_proper_convex S] {a : α} (ha : a ∈ S) (n : ℕ) :
  a^n ∈ S :=
begin
  induction n with n ih, { rw pow_zero, exact is_convex.one_mem S },
  rw pow_succ, exact is_convex.mul_mem ha ih,
end

-- move this
lemma is_convex.gpow_mem {α : Type*} [linear_ordered_comm_group α]
  (S : set α) [h : is_proper_convex S] {a : α} (ha : a ∈ S) :
  ∀ (n : ℤ), a^n ∈ S
| (int.of_nat n) := by { rw [gpow_of_nat], exact is_convex.pow_mem S ha n }
| -[1+n] := by { apply is_convex.inv_mem, exact is_convex.pow_mem S ha _ }

lemma height : height (units nnreal) = 1 :=
begin
  refine cardinal.eq_one_iff_nonempty_subsingleton.mpr ⟨⟨⟨set.univ, _⟩⟩, ⟨_⟩⟩,
  { constructor, any_goals { intros, exact set.mem_univ _ },
    have h2 : (2:nnreal) ≠ 0 := by norm_num,
    let two : units nnreal := group_with_zero.mk₀ 2 (by norm_num),
    refine ⟨1, two, set.mem_univ _, set.mem_univ _, _⟩,
    rw [ne.def, units.ext_iff], show (1:nnreal) ≠ 2, by norm_num, },
  { suffices key : ∀ S : set (units nnreal), is_proper_convex S → S = set.univ,
    { intros S T, rw [subtype.ext, key S.1 S.2, key T.1 T.2], },
    intros S hS, resetI,
    rw set.eq_univ_iff_forall, intro y,
    cases le_total 1 y with Hy Hy,
    { rcases exists_one_lt S with ⟨x, hx, Hx⟩,
      obtain ⟨n, hn⟩ : ∃ (n : ℕ), y ≤ x^n := sorry,
      exact is_convex.mem_of_between' S (is_convex.one_mem S) (is_convex.pow_mem S hx _) Hy hn, },
    { rcases exists_lt_one S with ⟨x, hx, Hx⟩,
      obtain ⟨n, hn⟩ : ∃ (n : ℕ), x^n ≤ y := sorry,
      exact is_convex.mem_of_between hn Hy (is_convex.pow_mem S hx _) } }
end

end nnreal
