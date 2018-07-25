import analysis.topology.topological_structures
import valuations 
import valuation_spectrum

/- although strictly speaking the commented-out defintion here
   is a "correct" definition, note that it is
   not constant across equivalence classes of valuations! The "correct" notion of
   continuity for an arbitrary equivalence class of valuations is that the induced
   valuation taking values in the value group is continuous.
-/

universes u v w

namespace valuation 

def function_is_continuous {R : Type u} [comm_ring R] [topological_space R] [topological_ring R] 
  {Γ : Type v} [linear_ordered_comm_group Γ] (f : R → option Γ) [Hf : is_valuation f] :
  Prop := ∀ x : Γ, is_open {r : R | f r < x}

def is_continuous {R : Type u} [comm_ring R] [topological_space R] [topological_ring R] 
  {Γ : Type u} [linear_ordered_comm_group Γ] (v : valuation R Γ) : Prop := 
∀ x : Γ, x ∈ value_group v → is_open {r : R | v r < x}

-- definition of continuous depends on value group

end valuation 

namespace Spv 

def is_continuous {R : Type u} [comm_ring R] [topological_space R] [topological_ring R]
  (vs : Spv R) := ∃ (Γ : Type u) [linear_ordered_comm_group Γ],
  by exactI ∃ (v : valuation R Γ), (∀ r s : R, vs.val r s ↔ v r ≤ v s) ∧ valuation.is_continuous v 

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

end Spv 

#check Spv.is_continuous -- Spv.is_continuous : Spv ?M_1 → Prop

def Cont (R : Type) [comm_ring R] [topological_space R] [topological_ring R]
  := {vs : Spv R // Spv.is_continuous vs}

example (R : Type) [comm_ring R] [topological_space R] [topological_ring R] :
topological_space (Spv R) := by apply_instance -- works

--example (R : Type) [comm_ring R] [topological_space R] [topological_ring R] :
--topological_space (Cont R) := by apply_instance -- fails

instance (R : Type) [comm_ring R] [topological_space R] [topological_ring R] :
topological_space (Cont R) := subtype.topological_space
