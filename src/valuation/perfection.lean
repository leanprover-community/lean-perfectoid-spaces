import field_theory.perfect_closure

import for_mathlib.nnreal

import valuation.basic

lemma iterate_frobenius_apply {α : Type*} [monoid α] (p n : ℕ) (a : α) :
  (frobenius α p)^[n] a = a^p^n :=
begin
  induction n with n ih, {simp},
  rw [nat.iterate_succ', ih, frobenius_def, ← pow_mul, nat.pow_succ]
end

noncomputable theory

namespace valuation
variables {R : Type*} [comm_ring R]
variables (v : valuation R nnreal)

namespace perfection
open nnreal
variables (p : ℕ) [nat.prime p] [char_p R p]

private def f₀ : ℕ × R → nnreal :=
λ (x : ℕ × R), (v x.2)^(p^(-x.1 : ℤ) : ℝ)

private def hf₀ : ∀ (x₁ x₂ : ℕ × R) (h : perfect_closure.r R p x₁ x₂),
  f₀ v p x₁ = f₀ v p x₂
| x₁ x₂ (perfect_closure.r.intro _ n x) :=
show v x ^ (p ^ (-n : ℤ) : ℝ) = v (x ^ p) ^ (p ^ (-(↑n + 1) : ℤ) : ℝ),
from have hp : (p : ℝ) ≠ 0 := by exact_mod_cast nat.prime.ne_zero ‹_›,
by rw [valuation.map_pow, ← rpow_nat_cast, ← rpow_mul, neg_add_rev,
    fpow_add hp, ← mul_assoc, fpow_inv, mul_inv_cancel hp, one_mul]

def f : perfect_closure R p → nnreal :=
quot.lift (f₀ v p) (hf₀ v p)

lemma f_zero : f v p (0 : perfect_closure R p) = 0 :=
calc f v p (0 : perfect_closure R p) = quot.lift (f₀ v p) (hf₀ v p) (0 : perfect_closure R p) : rfl
  ... = (v (0:R))^(p^(-0:ℤ) : ℝ) : quot.lift_beta (f₀ v p) (hf₀ v p) (0, 0)
  ... = 0 : by rw [v.map_zero, neg_zero, fpow_zero, rpow_one]

lemma f_one : f v p (1 : perfect_closure R p) = 1 :=
calc f v p (1 : perfect_closure R p) = quot.lift (f₀ v p) (hf₀ v p) (1 : perfect_closure R p) : rfl
  ... = (v (1:R))^(p^(-0:ℤ) : ℝ) : quot.lift_beta (f₀ v p) (hf₀ v p) (0, 1)
  ... = 1 : by rw [v.map_one, neg_zero, fpow_zero, rpow_one]

lemma f_mul (r s : perfect_closure R p) : f v p (r * s) = f v p r * f v p s :=
quot.induction_on r $ λ ⟨m,x⟩, quot.induction_on s $ λ ⟨n,y⟩,
show f₀ v p (m + n, _) = f₀ v p (m,x) * f₀ v p (n,y), from
have hp : p ≠ 0 := nat.prime.ne_zero ‹_›,
have hpQ : (p : ℝ) ≠ 0 := by exact_mod_cast hp,
begin
  clear _fun_match _fun_match _x _x,
  dsimp only [f₀],
  simp only [iterate_frobenius_apply, v.map_mul, v.map_pow, mul_rpow],
  congr' 1,
  all_goals {
    rw [← rpow_nat_cast, ← rpow_mul, nat.cast_pow, ←fpow_of_nat, ← fpow_add hpQ],
    { congr, rw [int.coe_nat_add, neg_add], abel }, },
end

lemma f_add (r s : perfect_closure R p) :
  f v p (r + s) ≤ max (f v p r) (f v p s) :=
quot.induction_on r $ λ ⟨m,x⟩, quot.induction_on s $ λ ⟨n,y⟩,
show f₀ v p (m + n, _) ≤ max (f₀ v p (m,x)) (f₀ v p (n,y)), from
have hp : p ≠ 0 := nat.prime.ne_zero ‹_›,
have hpQ : (p : ℝ) ≠ 0 := by exact_mod_cast hp,
begin
  clear _fun_match _fun_match _x _x,
  dsimp only [f₀],
  rw [iterate_frobenius_apply, iterate_frobenius_apply],
  have h := v.map_add (x^p^n) (y^p^m),
  rw le_max_iff at h ⊢,
  cases h with h h; [ {left, rw add_comm m}, right],
  all_goals {
    conv_rhs at h { rw v.map_pow },
    refine le_trans (rpow_le_rpow _ h (fpow_nonneg_of_nonneg (nat.cast_nonneg p) _)) (le_of_eq _),
    rw [← rpow_nat_cast, ← rpow_mul, nat.cast_pow, ←fpow_of_nat, ← fpow_add hpQ],
    { congr, rw [int.coe_nat_add, neg_add], abel }, }
end

end perfection

section
variables (p : ℕ) [nat.prime p] [char_p R p]

def perfection : valuation (perfect_closure R p) nnreal :=
{ to_fun := perfection.f v p,
  map_zero' := perfection.f_zero v p,
  map_one' := perfection.f_one v p,
  map_mul' := perfection.f_mul v p,
  map_add' := perfection.f_add v p }

end

end valuation
