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

namespace valuation 

def is_continuous {R : Type*} [comm_ring R] [topological_space R] [topological_ring R] 
  {Γ : Type*} [linear_ordered_comm_group Γ] (v : valuation R Γ) : Prop := 
∀ x : Γ, x ∈ value_group v → is_open {r : R | v r < x}

end valuation 

namespace Spv 

def is_continuous {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]
  (vs : Spv R) := ∃ (Γ : Type*) [linear_ordered_comm_group Γ],
  by exactI ∃ (v : valuation R Γ), ∀ r s : R, vs.val r s ↔ v r ≤ v s ∧ valuation.is_continuous v 

theorem forall_continuous {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]
  (vs : Spv R) : Spv.is_continuous vs ↔ ∀ (Γ : Type*) [linear_ordered_comm_group Γ],
  by exactI ∀ (v : valuation R Γ), (∀ r s : R, vs.val r s ↔ v r ≤ v s → valuation.is_continuous v) := sorry 

end Spv 

def Cont (R : Type) [comm_ring R] [topological_space R] [topological_ring R]
  := {vs : Spv R // Spv.is_continuous vs}
