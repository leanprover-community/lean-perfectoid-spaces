import analysis.topology.topological_structures
import valuations 
import valuation_spectrum

/- although strictly speaking the commented-out defintion her
   is a "correct" definition, note that it is
   not constant across equivalence classes of valuations! The "correct" notion of
   continuity for an arbitrary equivalence class of valuations is that the induced
   valuation taking values in the value group is continuous.

   def BAD_is_continuous {R : Type} [comm_ring R] [topological_space R] [topological_ring R] 
  {α : Type} [linear_ordered_comm_group α] (f : R → option α) (Hf : is_valuation f) :
  Prop := ∀ x : α, is_open {r : R | f r < x}

-/    

universes u v w

namespace valuation 

def is_continuous {R : Type u} [comm_ring R] [topological_space R] [topological_ring R] 
  {Γ : Type u} [linear_ordered_comm_group Γ] (v : valuation R Γ) : Prop := 
∀ x : Γ, x ∈ value_group v → is_open {r : R | v r < x}

-- definition of continuous depends on value group

theorem is_continuous_equiv {R : Type u} [comm_ring R] [topological_space R] [topological_ring R] 
  {Γ : Type u} [linear_ordered_comm_group Γ] (v : valuation R Γ)
  {Δ : Type u} [linear_ordered_comm_group Δ] (w : valuation R Δ) :


end valuation 

namespace Spv 

def is_continuous {R : Type u} [comm_ring R] [topological_space R] [topological_ring R]
  (vs : Spv R) := ∃ (Γ : Type u) [linear_ordered_comm_group Γ],
  by exactI ∃ (v : valuation R Γ), (∀ r s : R, vs.val r s ↔ v r ≤ v s) ∧ valuation.is_continuous v 

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

def Cont (R : Type) [comm_ring R] [topological_space R] [topological_ring R]
  := {vs : Spv R // Spv.is_continuous vs}
