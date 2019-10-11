import valuation.basic

/-!
# Discrete valuations

We define discrete valuations
-/

universe variables u u₀ u₁

open_locale classical

namespace valuation
variables {R : Type u} [ring R]
variables {Γ₀   : Type u₀} [linear_ordered_comm_group_with_zero Γ₀]
variables {Γ'₀  : Type u₁} [linear_ordered_comm_group_with_zero Γ'₀]
variables (v : valuation R Γ₀) {v' : valuation R Γ'₀}

def is_non_discrete : Prop :=
∀ r : R, v r < 1 → ∃ s : R, v r < v s ∧ v s < 1

def is_discrete : Prop :=
∃ r : R, ∀ s : R, v s ≠ 0 → ∃ n : ℤ, v s = (v r)^n

namespace is_equiv
variable {v}

lemma is_non_discrete (h : v.is_equiv v') :
  v.is_non_discrete ↔ v'.is_non_discrete :=
begin
  apply forall_congr, intro r,
  apply imp_congr_ctx h.lt_one, intro hr,
  apply exists_congr, intro s,
  rw [h.lt_iff, h.lt_one]
end

-- This is not so trivial. But we don't need it atm.
-- lemma is_discrete (h : v.is_equiv v') :
--   v.is_discrete ↔ v'.is_discrete :=
-- begin
--   apply exists_congr, intro r,
--   apply forall_congr, intro s,
--   apply imp_congr_ctx h.ne_zero, intro hs,
--   apply exists_congr, intro n,
--   sorry
-- end

-- lemma trichotomy :
--   v.is_trivial ∨ v.is_discrete ∨ v.is_non_discrete :=
-- sorry

end is_equiv

end valuation
