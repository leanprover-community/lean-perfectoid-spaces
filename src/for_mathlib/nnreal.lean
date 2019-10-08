import data.real.nnreal
import analysis.complex.exponential

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

end nnreal
