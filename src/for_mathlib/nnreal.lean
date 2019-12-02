import data.real.nnreal
import analysis.complex.exponential

import for_mathlib.cardinal

import valuation.linear_ordered_comm_group_with_zero

namespace nnreal

@[simp] lemma coe_max (x y : nnreal) : ((max x y : nnreal) : ℝ) = max (x : ℝ) (y : ℝ) :=
by { delta max, split_ifs; refl }

-- Has already been declared.
-- @[simp, move_cast] lemma coe_pow (x : nnreal) (n : ℕ) : ((x^n : nnreal) : ℝ) = x^n :=
-- by { induction n with n ih, { refl }, simp [nat.succ_eq_add_one, pow_add, ih], }

noncomputable instance : has_pow nnreal ℝ :=
{ pow := λ x q, ⟨x^q, real.rpow_nonneg_of_nonneg x.2 q⟩ }

variables (a b c : nnreal) (x y : ℝ)

lemma rpow_mul : a^(x * y) = (a^x)^y :=
subtype.coe_ext.mpr $ real.rpow_mul a.2 _ _

lemma mul_rpow : (a*b)^x = a^x * b^x :=
subtype.coe_ext.mpr $ real.mul_rpow a.2 b.2

@[elim_cast] lemma rpow_nat_cast (n : ℕ) : a^(n:ℝ) = a^n :=
subtype.coe_ext.mpr $ by { rw coe_pow, exact real.rpow_nat_cast a n }

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

end nnreal
