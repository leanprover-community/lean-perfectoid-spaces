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
  cases i with i hi,
  rcases nat.exists_eq_succ_of_ne_zero (ne_of_gt hi) with ⟨i, rfl⟩,
  induction i with i IH, {assumption},
  have h : 0 < i + 1, {exact nat.succ_pos i},
  apply hp ⟨i+1, h⟩,
  exact IH _,
end

variables (Γ₀ : Type*)  [linear_ordered_comm_group_with_zero Γ₀]
open  linear_ordered_structure

lemma linear_ordered_comm_group_with_zero.pow_strict_mono (n : ℕ+) : strict_mono (λ x : Γ₀, x^(n : ℕ)) :=
begin
  intros x y h,
  induction n using pnat.induction_on with n ih, { simpa },
  { dsimp only [] at *,
    rw [pnat.add_coe, pnat.one_coe, pow_succ, pow_succ], -- here we miss some norm_cast attribute
    apply linear_ordered_structure.mul_lt_mul' h ih, }
end

lemma linear_ordered_comm_group_with_zero.pow_mono (n : ℕ+) : monotone (λ x : Γ₀, x^(n : ℕ)) :=
(linear_ordered_comm_group_with_zero.pow_strict_mono Γ₀ n).monotone

variables {Γ₀}
lemma linear_ordered_comm_group_with_zero.pow_le_pow {x y : Γ₀} {n : ℕ+} : x^(n : ℕ) ≤ y^(n : ℕ) ↔ x ≤ y :=
strict_mono.le_iff_le (linear_ordered_comm_group_with_zero.pow_strict_mono Γ₀ n)

end

namespace valuation
variables {R : Type*} [ring R]
variables {Γ₀   : Type*} [linear_ordered_comm_group_with_zero Γ₀]
variables (v : valuation R Γ₀)

instance : has_pow (valuation R Γ₀) ℕ+ :=
⟨λ v n, { to_fun := λ r, (v r)^(n : ℕ),
  map_one' := by rw [v.map_one, one_pow],
  map_mul' := λ x y, by rw [v.map_mul, mul_pow],
  map_zero' := show (v 0)^n.val = 0,
    by rw [valuation.map_zero, ← nat.succ_pred_eq_of_pos n.2, pow_succ, zero_mul],
  map_add' := begin
    intros x y,
    wlog vyx : v y ≤ v x using x y,
    { have : (v y)^(n:ℕ) ≤ (v x)^(n:ℕ),
        by apply linear_ordered_comm_group_with_zero.pow_mono ; assumption,
      rw max_eq_left this,
      apply linear_ordered_comm_group_with_zero.pow_mono,
      convert v.map_add x y,
      rw max_eq_left vyx },
    { rwa [add_comm, max_comm] },
  end }⟩

@[simp] protected lemma pow_one : v^(1:ℕ+) = v :=
ext $ λ r, pow_one (v r)

protected lemma pow_mul (m n : ℕ+) : v^(m*n) = (v^m)^n :=
ext $ λ r, pow_mul (v r) m n

lemma is_equiv_of_pow (v : valuation R Γ₀) (m n : ℕ+) : is_equiv (v^m) (v^n) :=
begin
  intros r s,
  change (v r) ^ (m:ℕ) ≤ (v s) ^ (m:ℕ) ↔ _,
  rw [← linear_ordered_comm_group_with_zero.pow_le_pow, ← pow_mul, ← pow_mul,
      mul_comm, pow_mul, pow_mul, linear_ordered_comm_group_with_zero.pow_le_pow],
  { exact iff.rfl }
end

lemma is_equiv_of_pow_self (v : valuation R Γ₀) (n : ℕ+) : is_equiv v (v^n) :=
by simpa using v.is_equiv_of_pow 1 n

end valuation
