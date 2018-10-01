import analysis.topology.topological_structures
import valuation_spectrum

universes u₁ u₂ u₃

namespace valuation 
variables {R : Type u₁} [comm_ring R] [topological_space R] [topological_ring R]
variables {Γ : Type u₂} [linear_ordered_comm_group Γ]

-- this definition should only be applied to valuations such that Gamma is the value group;
-- without this assumption the definition is meaningless (e.g. one can have two equivalent
-- valuations, one continuous and one not).
def function_is_continuous (v : R → with_zero Γ) [is_valuation v] : Prop :=
∀ x : Γ, x ∈ value_group_v v → is_open {r : R | v r < x}

-- This definition is the correct definition of continuity of a valuation. It's constant
-- across equivalence classes (although at the time of writing I've not proved this)
def is_continuous (v : valuation R Γ) : Prop := function_is_continuous v

lemma is_continuous_of_equiv_is_continuous {Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁] {Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂]
 {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} (heq : valuation.is_equiv v₁ v₂) (H : v₁.is_continuous) : v₂.is_continuous :=
begin
  dsimp [is_continuous,valuation.function_is_continuous] at H ⊢,
  intros x hx,
  sorry
end

end valuation

namespace Valuation
variables {R : Type u₁} [comm_ring R] [topological_space R] [topological_ring R] [decidable_eq R]

def is_continuous (v : Valuation R) : Prop := valuation.function_is_continuous v

lemma is_continuous_of_equiv_is_continuous {v₁ v₂ : Valuation R} (heq : v₁ ≈ v₂) (H : v₁.is_continuous) : v₂.is_continuous :=
valuation.is_continuous_of_equiv_is_continuous heq H

end Valuation

namespace Spv 

variables {R : Type u₁} [comm_ring R] [topological_space R] [topological_ring R] [decidable_eq R]

-- This is a mathematically correct definition of what it means for an equivalence
-- class of valuations to be continuous.
def is_continuous : Spv R → Prop :=
Spv.lift (λ v : Valuation R, v.is_continuous)
(λ v₁ v₂ heq, begin
ext, split; intro h,
exact Valuation.is_continuous_of_equiv_is_continuous heq h,
exact Valuation.is_continuous_of_equiv_is_continuous (setoid.symm heq) h,
end)

--  ∃ (Γ : Type u) [linear_ordered_comm_group Γ],
--   by exactI ∃ (v : valuation R Γ), (∀ r s : R, vs.val r s ↔ v r ≤ v s) ∧ valuation.is_continuous v

-- What we unfortunately do not yet have is a proof that this definition is equivalent to the
-- condition that *all* valuations giving rise to `vs` are continuous.

/-
Proof of the below two theorems needs stuff like Wedhorn 1.27 which we didn't do yet.

theorem continuous_iff_out_continuous {R : Type u} [comm_ring R] [topological_space R]
  [topological_ring R] [decidable_eq R] {Γ2 : Type v} [linear_ordered_comm_group Γ2]
  (v : valuation R Γ2): 
Spv.is_continuous (Spv.mk v) ↔ valuation.function_is_continuous (valuation.minimal_valuation v.f) := sorry

theorem forall_continuous {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]
  (vs : Spv R) : Spv.is_continuous vs ↔ ∀ (Γ : Type*) [linear_ordered_comm_group Γ],
  by exactI ∀ (v : valuation R Γ), (∀ r s : R, vs.val r s ↔ v r ≤ v s) → valuation.is_continuous v :=
begin
  split,
  { intros Hvs Γ iΓ v Hv,
    cases Hvs with Δ HΔ,
    cases HΔ with iΔ HΔ,
    cases HΔ with w Hw,
    -- this is the hard part
    -- our given w is continuous -> all v are continuous
    intros g Hg,
    sorry 
  },
  { intro H,
    cases vs with ineq Hineq,
    cases Hineq with Γ HΓ,
    cases HΓ with iΓ HΓ,
    cases HΓ with v Hv,
    unfold is_continuous,
    existsi Γ,
    existsi iΓ,
    existsi v,
    split,
      exact Hv,
    apply H,
    exact Hv
  }
end 
-/

end Spv 

def Cont (R : Type) [comm_ring R] [topological_space R] [topological_ring R] [decidable_eq R]
  := {v : Spv R // Spv.is_continuous v}

instance (R : Type) [comm_ring R] [topological_space R] [topological_ring R] [decidable_eq R] :
topological_space (Cont R) := by unfold Cont; apply_instance

/-
Wedhorn p59:
  A valuation v on A is continuous if and only if for all γ ∈ Γ_v (the value group),
  the set A_{≤γ} := { a ∈ A ; v(a) ≥ γ } is open in A. 
 
  This is a typo -- should be v(a) ≤ γ. 
-/