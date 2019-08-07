import valuation.basic
import field_theory.perfect_closure

lemma iterate_frobenius_apply {α : Type*} [monoid α] (p n : ℕ) (a : α) :
  (frobenius α p)^[n] a = a^p^n :=
begin
  induction n with n ih, {simp},
  rw [nat.iterate_succ', ih, frobenius_def, ← pow_mul, nat.pow_succ]
end

namespace valuation
variables {R : Type*} [comm_ring R]
variables {Γ : Type*} [linear_ordered_comm_group Γ]
variables (v : valuation R Γ)

namespace perfection
variables (p : ℕ) [nat.prime p] [char_p R p]
variables [module ℚ (additive Γ)]

private def pow : with_zero Γ → ℚ → with_zero Γ
| 0        n := 0
| (some γ) n := (some ((n • (γ : additive Γ) : additive Γ) : Γ) : with_zero Γ)

def pow_inst : has_pow (with_zero Γ) ℚ := ⟨pow⟩

local attribute [instance] pow_inst

@[simp] lemma zero_pow (n : ℚ) : (0 : with_zero Γ) ^ n = 0 := rfl

lemma coe_pow (γ : Γ) (n : ℚ) :
  (γ : with_zero Γ) ^ n = (some ((n • (γ : additive Γ) : additive Γ) : Γ) : with_zero Γ) :=
rfl

@[simp] lemma coe_pow_zero (γ : Γ) : (γ : with_zero Γ) ^ (0 : ℚ) = 1 :=
by { rw [coe_pow, zero_smul], refl }

lemma pow_zero (γ : with_zero Γ) (h : γ ≠ 0) : γ^(0:ℚ) = 1 :=
by { with_zero_cases γ, refl }

@[simp] lemma one_pow (n : ℚ) : (1 : with_zero Γ) ^ n = 1 :=
by { rw [with_zero.coe_one', coe_pow], congr' 1, show n • (0 : additive Γ) = 0, exact smul_zero n }

@[simp] lemma pow_one (γ : with_zero Γ) : γ^(1:ℚ) = γ :=
by { with_zero_cases γ, rw [coe_pow, one_smul], refl }

lemma pow_add (γ : with_zero Γ) (m n : ℚ) :
  γ^(m+n) = γ^m * γ^n :=
by { with_zero_cases γ, rw [coe_pow, add_smul], refl }

lemma pow_pow (γ : with_zero Γ) (m n : ℚ) :
  (γ^m)^n = γ^(m*n) :=
by { with_zero_cases γ, rw [coe_pow _ (m * n), mul_comm, mul_smul], refl }

lemma mul_pow (γ₁ γ₂ : with_zero Γ) (n : ℚ) :
  (γ₁ * γ₂)^n = γ₁^n * γ₂^n :=
by { with_zero_cases γ₁ γ₂, show some _ = some (_ * _), congr' 1, convert smul_add _ _ _ }

variable (Γ)
lemma pow_strict_mono.aux (n : ℕ) (h : 0 < n) :
  @strict_mono _ _ _ (show has_lt Γ, by apply_instance)
  (λ γ : Γ, @has_scalar.smul ℚ (additive Γ) _ n γ) :=
begin
  cases n with n,
  { exfalso, exact nat.not_lt_zero _ h },
  clear h,
  induction n with n ih, { intros _ _ H, simpa using H },
  intros γ₁ γ₂ H, specialize ih γ₁ γ₂ H,
  simp only [add_smul, one_smul, nat.cast_succ] at ih ⊢,
  exact linear_ordered_structure.mul_lt_mul ih H
end

lemma pow_strict_mono (n : ℚ) (h : 0 < n) :
  strict_mono (λ γ : with_zero Γ, γ^n) :=
begin
  have hn : n = (n.num.nat_abs : ℚ) * (n.denom)⁻¹,
  { rw ←rat.num_pos_iff_pos at h,
    cases n with n d p c, dsimp only at *,
    rw [rat.num_denom', rat.mk_eq_div, div_eq_mul_inv],
    rw_mod_cast (int.eq_nat_abs_of_zero_le (le_of_lt h)), refl },
  intros γ₁ γ₂ H,
  with_zero_cases γ₁ γ₂,
  { exact with_zero.zero_lt_coe },
  { erw [coe_pow, coe_pow, with_zero.coe_lt_coe, hn, mul_smul, mul_smul],
    refine pow_strict_mono.aux Γ _
      (int.nat_abs_pos_of_ne_zero $ rat.num_ne_zero_of_ne_zero (ne_of_lt h).symm) _ _ _,
    rw ← (pow_strict_mono.aux Γ n.denom n.pos).lt_iff_lt,
    dsimp only,
    have : (n.denom : ℚ) ≠ 0 := by exact_mod_cast (nat.pos_iff_ne_zero.mp n.pos),
    simpa only [smul_smul, mul_inv_cancel this, one_smul] using H }
end
variable {Γ}

lemma pow_mono (n : ℚ) (h : 0 ≤ n) (γ₁ γ₂ : with_zero Γ) (H : γ₁ ≤ γ₂) : γ₁^n ≤ γ₂^n :=
begin
  with_zero_cases γ₁ γ₂,
  by_cases hn : 0 = n,
  { rw [← hn, pow_zero _ (with_zero.coe_ne_zero), pow_zero _ (with_zero.coe_ne_zero)],
    exact le_refl _ },
  have : 0 < n := lt_of_le_of_ne h hn,
  rwa [(pow_strict_mono Γ n this).le_iff_le, with_zero.coe_le_coe]
end

lemma pow_eq_pow_coe (γ : with_zero Γ) (h : γ ≠ 0) (n : ℕ) :
  γ^n = γ^(n : ℚ) :=
begin
  with_zero_cases γ,
  { induction n with n ih,
    { rw [_root_.pow_zero, nat.cast_zero, coe_pow_zero] },
    { rw [pow_succ', nat.cast_succ, pow_add, pow_one, ih] } }
end

lemma pow_eq_pow_coe' (γ : with_zero Γ) (n : ℕ) (h : n ≠ 0) :
  γ^n = γ^(n : ℚ) :=
begin
  with_zero_cases γ,
  { induction n with n ih, { exfalso, exact h rfl }, { rw [pow_succ, zero_mul] } },
  { apply pow_eq_pow_coe, exact with_zero.coe_ne_zero }
end

private def f₀ : ℕ × R → with_zero Γ :=
λ (x : ℕ × R), (v x.2)^(p^(-x.1 : ℤ) : ℚ)

private def hf₀ : ∀ (x₁ x₂ : ℕ × R) (h : perfect_closure.r R p x₁ x₂),
  f₀ v p x₁ = f₀ v p x₂
| x₁ x₂ (perfect_closure.r.intro _ n x) :=
show v x ^ (p ^ (-n : ℤ) : ℚ) = v (x ^ p) ^ (p ^ (-(↑n + 1) : ℤ) : ℚ),
from have hp : (p : ℚ) ≠ 0 := by exact_mod_cast nat.prime.ne_zero ‹_›,
by rw [valuation.map_pow, pow_eq_pow_coe' _ p (nat.prime.ne_zero ‹_›), pow_pow,
  add_comm, neg_add, fpow_add hp, ← mul_assoc, fpow_inv, mul_inv_cancel hp, one_mul]

def f : perfect_closure R p → with_zero Γ :=
quot.lift (f₀ v p) (hf₀ v p)

private lemma f_zero : f v p (0 : perfect_closure R p) = 0 :=
calc f v p (0 : perfect_closure R p) = quot.lift (f₀ v p) (hf₀ v p) (0 : perfect_closure R p) : rfl
  ... = (v (0:R))^(p^(-0:ℤ) : ℚ) : quot.lift_beta (f₀ v p) (hf₀ v p) (0, 0)
  ... = 0 : by rw [v.map_zero, neg_zero, fpow_zero, pow_one]

private lemma f_one : f v p (1 : perfect_closure R p) = 1 :=
calc f v p (1 : perfect_closure R p) = quot.lift (f₀ v p) (hf₀ v p) (1 : perfect_closure R p) : rfl
  ... = (v (1:R))^(p^(-0:ℤ) : ℚ) : quot.lift_beta (f₀ v p) (hf₀ v p) (0, 1)
  ... = 1 : by rw [v.map_one, neg_zero, fpow_zero, pow_one]

private lemma f_mul (r s : perfect_closure R p) : f v p (r * s) = f v p r * f v p s :=
quot.induction_on r $ λ ⟨m,x⟩, quot.induction_on s $ λ ⟨n,y⟩,
show f₀ v p (m + n, _) = f₀ v p (m,x) * f₀ v p (n,y), from
have hp : p ≠ 0 := nat.prime.ne_zero ‹_›,
have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp,
begin
  clear _fun_match _fun_match _x _x,
  dsimp only [f₀],
  simp only [iterate_frobenius_apply, v.map_mul, v.map_pow, mul_pow],
  congr' 1,
  all_goals {
    rw [pow_eq_pow_coe', pow_pow, nat.cast_pow, ←fpow_of_nat, ← fpow_add hpQ],
    { congr, rw [int.coe_nat_add, neg_add], abel },
    rw ← nat.pos_iff_ne_zero at hp ⊢,
    exact nat.pow_pos hp _ }
end

private lemma f_add (r s : perfect_closure R p) :
  f v p (r + s) ≤ f v p r ∨ f v p (r + s) ≤ f v p s :=
quot.induction_on r $ λ ⟨m,x⟩, quot.induction_on s $ λ ⟨n,y⟩,
show f₀ v p (m + n, _) ≤ f₀ v p (m,x) ∨ f₀ v p (m + n, _) ≤ f₀ v p (n,y), from
have hp : p ≠ 0 := nat.prime.ne_zero ‹_›,
have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp,
begin
  clear _fun_match _fun_match _x _x,
  dsimp only [f₀],
  rw [iterate_frobenius_apply, iterate_frobenius_apply],
  cases v.map_add (x^p^n) (y^p^m); [ {left, rw add_comm m}, right],
  all_goals {
    conv_rhs at h { rw v.map_pow },
    refine le_trans (pow_mono _ (fpow_nonneg_of_nonneg (nat.cast_nonneg p) _) _ _ h) (le_of_eq _),
    rw [pow_eq_pow_coe', pow_pow, nat.cast_pow, ←fpow_of_nat, ← fpow_add hpQ],
    { congr, rw [int.coe_nat_add, neg_add], abel },
    rw ← nat.pos_iff_ne_zero at hp ⊢,
    exact nat.pow_pos hp _ }
end

lemma is_valuation : is_valuation (f v p) :=
{ map_zero := f_zero v p,
  map_one := f_one v p,
  map_mul := f_mul v p,
  map_add := f_add v p }

end perfection

section
variables (p : ℕ) [nat.prime p] [char_p R p]
variables [module ℚ (additive Γ)]

def perfection : valuation (perfect_closure R p) Γ :=
{ val := perfection.f v p,
  property := perfection.is_valuation v p }

end

end valuation
