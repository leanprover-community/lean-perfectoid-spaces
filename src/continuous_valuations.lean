import analysis.topology.topological_structures
import valuations 
import valuation_spectrum

universes u v w

namespace valuation 

-- this definition should only be applied to valuations such that Gamma is the value group;
-- without this assumption the definition is meaningless (e.g. one can have two equivalent
-- valuations, one continuous and one not).
def function_is_continuous {R : Type u} [comm_ring R] [topological_space R] [topological_ring R] 
  {Γ : Type v} [linear_ordered_comm_group Γ] (f : R → option Γ) [Hf : is_valuation f] :
  Prop := ∀ x : Γ, is_open {r : R | f r < x}

-- This definition is the correct definition of continuity of a valuation. It's constant
-- across equivalence classes (although at the time of writing I've not proved this)
def is_continuous {R : Type u} [comm_ring R] [topological_space R] [topological_ring R] 
  {Γ : Type u} [linear_ordered_comm_group Γ] (v : valuation R Γ) : Prop := 
∀ x : Γ, x ∈ value_group v → is_open {r : R | v r < x}

end valuation 

namespace Spv 

-- This is a mathematically correct definition of what it means for a valuation to be continuous.
def is_continuous {R : Type u} [comm_ring R] [topological_space R] [topological_ring R]
  (vs : Spv R) := ∃ (Γ : Type u) [linear_ordered_comm_group Γ],
  by exactI ∃ (v : valuation R Γ), (∀ r s : R, vs.val r s ↔ v r ≤ v s) ∧ valuation.is_continuous v 
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

def Cont (R : Type) [comm_ring R] [topological_space R] [topological_ring R]
  := {vs : Spv R // Spv.is_continuous vs}

instance (R : Type) [comm_ring R] [topological_space R] [topological_ring R] :
topological_space (Cont R) := by unfold Cont; apply_instance
