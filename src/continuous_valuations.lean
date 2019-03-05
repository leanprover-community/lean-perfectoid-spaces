import topology.algebra.topological_structures
import valuation_spectrum

universes u₁ u₂ u₃

namespace valuation
variables {R : Type u₁} [comm_ring R] [topological_space R] [topological_ring R]
variables {Γ : Type u₂} [linear_ordered_comm_group Γ]

/-- Continuity of a valuation. -/
def is_continuous (v : valuation R Γ) : Prop :=
∀ x : value_group v, is_open {r : R | canonical_valuation v r < x}

-- We could probably prove this now, but I didn't do it yet.
lemma is_continuous_of_equiv_is_continuous {Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁]
  {Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂]
  {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} (heq : valuation.is_equiv v₁ v₂)
  (H : v₁.is_continuous) : v₂.is_continuous :=
begin
  intro g,
  -- need map value_group v₁ → value_group v₂ coming from equiv
  -- actually, we probably have this now.
  sorry
end

end valuation

-- Now we can define what it means for `v : Spv R` to be continuous
-- using Spv.lift.

-- KMB has not looked below this point.
#exit
namespace Valuation
variables {R : Type u₁} [comm_ring R] [topological_space R] [topological_ring R] [decidable_eq R]

def is_continuous (v : Valuation R) : Prop := valuation.function_is_continuous v

lemma is_continuous_of_equiv_is_continuous {v₁ v₂ : Valuation R} (heq : v₁ ≈ v₂) (H : v₁.is_continuous) : v₂.is_continuous :=
valuation.is_continuous_of_equiv_is_continuous heq H

end Valuation

namespace Spv

variables {R : Type u₁} [comm_ring R] [topological_space R] [topological_ring R] [decidable_eq R]

/-
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

variable (R)
def Cont := {v : Spv R | (v : Valuation R).is_continuous}
variable {R}

def mk_mem_Cont {v : Valuation R} : mk v ∈ Cont R ↔ v.is_continuous :=
begin
split; intro h; refine Valuation.is_continuous_of_equiv_is_continuous _ h,
exact out_mk, exact (setoid.symm out_mk),
end

instance Cont.topological_space : topological_space (Cont R) := by apply_instance

end Spv

/-
Wedhorn p59:
  A valuation v on A is continuous if and only if for all γ ∈ Γ_v (the value group),
  the set A_{≤γ} := { a ∈ A ; v(a) ≥ γ } is open in A.

  This is a typo -- should be v(a) ≤ γ.
-/
