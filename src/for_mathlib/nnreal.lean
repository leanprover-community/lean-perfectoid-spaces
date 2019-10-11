import data.real.nnreal
import analysis.complex.exponential

import for_mathlib.cardinal

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

section pow_enat
noncomputable theory
open_locale classical
open function

/--If r is a nonnegative real number and n an enat,
than b^n is defined as expected if n is natural, and b^infty = 0.
Hence, this should only be applied to b < 1.-/
def pow_enat : has_pow nnreal enat :=
⟨λ r n, if h : n.dom then (r^n.get h) else 0⟩

local attribute [instance] pow_enat

lemma pow_enat_def {b : nnreal} {n : enat} :
  b^n = if h : n.dom then (b^n.get h) else 0 := rfl

@[simp] lemma pow_enat_top (b : nnreal) :
  b ^ (⊤ : enat) = 0 :=
begin
  rw [pow_enat_def, dif_neg], exact not_false
end

@[simp] lemma pow_enat_zero (b : nnreal) :
  b ^ (0 : enat) = 1 :=
begin
  rw [pow_enat_def, dif_pos, enat.get_zero, pow_zero],
  exact trivial,
end

@[simp] lemma pow_enat_one (b : nnreal) :
  b ^ (1 : enat) = b :=
begin
  rw [pow_enat_def, dif_pos, enat.get_one, pow_one],
  exact trivial,
end

@[simp] lemma pow_enat_add (b : nnreal) (m n : enat) :
  b ^ (m + n) = b ^ m * b ^ n :=
begin
  iterate 3 {rw pow_enat_def},
  by_cases hm : m.dom,
  { by_cases hn : n.dom,
    { have hmn : (m + n).dom := ⟨hm, hn⟩,
      rw [dif_pos hm, dif_pos hn, dif_pos,
          subtype.coe_ext, nnreal.coe_mul, ← nnreal.coe_mul, ← pow_add, enat.get_add, add_comm],
      exact hmn, },
    { rw [dif_pos hm, dif_neg hn, dif_neg, mul_zero],
      contrapose! hn with H, exact H.2 } },
  { rw [dif_neg hm, dif_neg, zero_mul],
    contrapose! hm with H, exact H.1 },
end

@[simp] lemma pow_enat_le (b : nnreal) (h₁ : b ≠ 0) (h₂ : b ≤ 1) (m n : enat) (h : m ≤ n) :
  b ^ n ≤ b ^ m :=
begin
  iterate 2 {rw pow_enat_def},
  by_cases hn : n.dom,
  { rw ← enat.coe_get hn at h,
    have hm : m.dom := enat.dom_of_le_some h,
    rw [← enat.coe_get hm, enat.coe_le_coe] at h,
    rw [dif_pos hm, dif_pos hn],
    rw [← linear_ordered_structure.inv_le_inv _ h₁, inv_one'] at h₂,
    have := pow_le_pow h₂ h,
    -- We need lots of norm_cast lemmas
    rwa [nnreal.coe_le, nnreal.coe_pow, nnreal.coe_pow, nnreal.coe_inv, ← pow_inv, ← pow_inv,
      ← nnreal.coe_pow, ← nnreal.coe_pow, ← nnreal.coe_inv, ← nnreal.coe_inv, ← nnreal.coe_le,
      linear_ordered_structure.inv_le_inv] at this,
    any_goals { exact one_ne_zero },
    all_goals { contrapose! h₁ },
    any_goals { exact subtype.val_injective h₁ },
    any_goals { apply group_with_zero.pow_eq_zero, assumption } },
  { rw dif_neg hn, exact zero_le _ }
end

@[simp] lemma pow_enat_lt (b : nnreal) (h₁ : b ≠ 0) (h₂ : b < 1) (m n : enat) (h : m < n) :
  b ^ n < b ^ m :=
begin
  iterate 2 {rw pow_enat_def},
  by_cases hn : n.dom,
  { rw ← enat.coe_get hn at h,
    have hm : m.dom := enat.dom_of_le_some (le_of_lt h),
    rw [← enat.coe_get hm, enat.coe_lt_coe] at h,
    rw [dif_pos hm, dif_pos hn],
    rw [← linear_ordered_structure.inv_lt_inv _ h₁, inv_one'] at h₂,
    have := pow_lt_pow h₂ h,
    -- We need lots of norm_cast lemmas
    rwa [nnreal.coe_lt, nnreal.coe_pow, nnreal.coe_pow, nnreal.coe_inv, ← pow_inv, ← pow_inv,
      ← nnreal.coe_pow, ← nnreal.coe_pow, ← nnreal.coe_inv, ← nnreal.coe_inv, ← nnreal.coe_lt,
      linear_ordered_structure.inv_lt_inv] at this,
    any_goals { exact one_ne_zero },
    all_goals { contrapose! h₁ },
    any_goals { exact subtype.val_injective h₁ },
    all_goals { apply group_with_zero.pow_eq_zero, assumption } },
  { rw dif_neg hn,
    have : n = ⊤ := roption.eq_none_iff'.mpr hn, subst this,
    replace h := ne_of_lt h,
    rw enat.ne_top_iff at h, rcases h with ⟨m, rfl⟩,
    rw dif_pos, swap, {trivial},
    apply pow_pos,
    exact lt_of_le_of_ne b.2 h₁.symm }
end

@[simp] lemma pow_enat_inj (b : nnreal) (h₁ : b ≠ 0) (h₂ : b < 1) :
  injective ((^) b : enat → nnreal) :=
begin
  intros m n h,
  wlog H : m ≤ n,
  rcases lt_or_eq_of_le H with H|rfl,
  { have := pow_enat_lt b h₁ h₂ m n H,
    exfalso, exact ne_of_lt this h.symm, },
  { refl },
end

end pow_enat

end nnreal
