/-
Stuff in this file should eventually go to the valuation folder,
but keeping it here is faster at this point.
-/

import valuation.basic

local attribute [instance, priority 0] classical.decidable_linear_order

section
@[elab_as_eliminator] protected lemma pnat.induction_on {p : ℕ+ → Prop}
  (i : ℕ+) (hz : p 1) (hp : ∀j : ℕ+, p j → p (j + 1)) : p i :=
begin
  sorry
end

variables (Γ₀ : Type*)  [linear_ordered_comm_group_with_zero Γ₀]
open  linear_ordered_structure

lemma linear_ordered_comm_group_with_zero.pow_strict_mono (n : ℕ+) : strict_mono (λ x : Γ₀, x^(n : ℕ)) :=
begin
  intros x y h,
  induction n using pnat.induction_on with n ih,
  { simpa },
  { simp only [] at *,
    rw [pnat.add_coe, pnat.one_coe, pow_succ, pow_succ], -- here we miss some norm_cast attribute
    by_cases hx : x = 0,
    { simp [hx] at *,

      sorry },
    { -- do x * ih (using that x ≠ 0) and then h * y^n (using 0 < x^n < y^n)
      sorry } }
end

lemma linear_ordered_comm_group_with_zero.pow_mono (n : ℕ+) : monotone (λ x : Γ₀, x^(n : ℕ)) :=
(linear_ordered_comm_group_with_zero.pow_strict_mono Γ₀ n).monotone

variables {Γ₀}
lemma linear_ordered_comm_group_with_zero.pow_le_pow {x y : Γ₀} {n : ℕ+} : x^(n : ℕ) ≤ y^(n : ℕ) ↔ x ≤ y :=
strict_mono.le_iff_le (linear_ordered_comm_group_with_zero.pow_strict_mono Γ₀ n)

end

variables {R : Type*} [ring R]

variables {Γ₀   : Type*}  [linear_ordered_comm_group_with_zero Γ₀]

instance valuation.pow : has_pow (valuation R Γ₀) ℕ+ :=
⟨λ v n, { to_fun := λ r, (v r)^n.val,
  map_one' := by rw [v.map_one, one_pow],
  map_mul' := λ x y, by rw [v.map_mul, mul_pow],
  map_zero' := by rw [valuation.map_zero, ← nat.succ_pred_eq_of_pos n.2, pow_succ, zero_mul],
  map_add' := begin
    intros x y,
    wlog vyx : v y ≤ v x using x y,
    { have : (v y)^n.val ≤ (v x)^n.val, by apply linear_ordered_comm_group_with_zero.pow_mono ; assumption,
      rw max_eq_left this,
      apply linear_ordered_comm_group_with_zero.pow_mono,
      convert v.map_add x y,
      rw max_eq_left vyx },
    { rwa [add_comm, max_comm] },
  end }⟩
