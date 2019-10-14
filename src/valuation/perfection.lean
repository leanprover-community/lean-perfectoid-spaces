import field_theory.perfect_closure

import for_mathlib.nnreal

import valuation.basic
import valuation.discrete

lemma iterate_frobenius_apply {α : Type*} [monoid α] (p n : ℕ) (a : α) :
  (frobenius α p)^[n] a = a^p^n :=
begin
  induction n with n ih, {simp},
  rw [nat.iterate_succ', ih, frobenius_def, ← pow_mul, nat.pow_succ]
end

noncomputable theory
open_locale classical

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
variables (R) (p : ℕ) [hp : p.prime] [char_p R p]

include hp

def perfection : valuation (perfect_closure R p) nnreal :=
{ to_fun := perfection.f v p,
  map_zero' := perfection.f_zero v p,
  map_one' := perfection.f_one v p,
  map_mul' := perfection.f_mul v p,
  map_add' :=
  begin
    -- TODO(jmc): This is really ugly. But Lean doesn't cooperate.
    -- It finds two instances that aren't defeq.
    intros r s,
    convert perfection.f_add v p r s,
    delta classical.decidable_linear_order nnreal.decidable_linear_order,
    congr,
  end }

lemma perfection_apply (n : ℕ) (r : R) :
  v.perfection R p (quot.mk _ ⟨n, r⟩) = v r ^ (p ^ (-n : ℤ) : ℝ) := rfl

@[simp] lemma perfection_of (r : R) :
  v.perfection R p (perfect_closure.of R p r) = v r :=
show (v r) ^ _ = v r,
by simp only [fpow_zero, int.coe_nat_zero, nnreal.rpow_one, neg_zero]

end

namespace perfection
open filter real

lemma tendsto_pow_zero {x : ℝ} (hx : x ≠ 0) : tendsto (λ ε, x^ε) (nhds (0 : ℝ)) (nhds 1) :=
begin
  convert (continuous_rpow_of_ne_zero (λ y, hx) continuous_const continuous_id).continuous_at,
  simp
end

-- TODO: rename?
lemma johan {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) : ∃ r : ℝ, 0 < r ∧ x^r < 1 + ε :=
begin
  have lim := tendsto_pow_zero (by linarith : x ≠ 0),
  rw metric.tendsto_nhds_nhds at lim,
  simp only [dist_0_eq_abs, dist_eq, sub_zero] at lim,
  rcases lim ε hε with ⟨r, rpos, H⟩,
  use [r/2, by linarith],
  have : abs (r/2) < r, by rw abs_of_nonneg ; linarith,
  specialize H this,
  have : 0 ≤ x ^ (r / 2) - 1,
  { suffices : 1 ≤ x^(r/2), by linarith,
    apply one_le_rpow ; linarith },
  rw abs_of_nonneg this at H,
  linarith
end

variables (K : Type*) [discrete_field K] (p : ℕ) [hp : p.prime] [char_p K p]
include hp

lemma non_discrete (v : valuation K nnreal) (hv : ¬ v.is_trivial) (ε : nnreal) (h : 0 < ε) :
  ∃ x : perfect_closure K p, 1 < v.perfection K p x ∧ v.perfection K p x < 1 + ε :=
begin
  obtain ⟨x, hx⟩ : ∃ x, 1 < v x,
  { delta is_trivial at hv, push_neg at hv, rcases hv with ⟨x, h₁, h₂⟩,
    by_cases hx : 1 < v x, { use [x,hx] },
    use x⁻¹,
    rw [v.map_inv, ← linear_ordered_structure.inv_lt_inv _ _, inv_inv'', inv_one'],
    { push_neg at hx, exact lt_of_le_of_ne hx h₂ },
    { contrapose! h₁, rwa nnreal.inv_eq_zero at h₁ },
    { exact one_ne_zero } },
  suffices : ∃ n : ℕ, (v x)^(p^(-n : ℤ) : ℝ) < 1 + ε,
  { rcases this with ⟨n, hn⟩,
    refine ⟨quot.mk (perfect_closure.r K p) (n,x), _, hn⟩,
    change 1 < (v x)^(p^(-n : ℤ) : ℝ),
    rw nnreal.coe_lt,
    apply real.one_lt_rpow hx,
    apply fpow_pos_of_pos,
    exact_mod_cast hp.pos, },
  rcases johan hx h with ⟨r, hr, H⟩,
  -- TODO: the next block is copied from examples/padics, should we extract it?
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (p : ℝ)^-(n : ℤ) < r,
    { have hp : (1:ℝ) < p := by exact_mod_cast nat.prime.one_lt ‹_›,
      obtain ⟨n, hn⟩ : ∃ (n:ℕ), r⁻¹ < p^n := pow_unbounded_of_one_lt r⁻¹ hp,
      use n,
      have hp' : (0:ℝ) < p^n,
      { rw ← fpow_of_nat, apply fpow_pos_of_pos, exact_mod_cast nat.prime.pos ‹_› },
      rw [inv_lt hr hp', inv_eq_one_div] at hn,
      rwa [fpow_neg, fpow_of_nat], },
  use n,
  transitivity (v x)^r,
  exact rpow_lt_rpow_of_exponent_lt hx hn,
  assumption
end

-- lemma non_discrete' (v : valuation K nnreal) (hv : ¬ v.is_trivial) :
--   (v.perfection K p).is_non_discrete :=
-- begin
--   intros r hr,
--   by_cases H : v.perfection K p r = 0,
--   { rcases exists_lt_one_of_not_trivial _ hv with ⟨x, h₁, h₂⟩,
--     rw H, refine ⟨(perfect_closure.of K p x), _, _⟩,
--     { contrapose! h₂, rwa [perfection_of, le_zero_iff_eq] at h₂ },
--     { rwa perfection_of } },
--   sorry
--   -- { refine ⟨perfect_field.pth_root 1 r, _, _⟩,
--   --   {  },
--   --   {  } }
-- end

end perfection

end valuation
