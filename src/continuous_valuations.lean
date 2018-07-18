import analysis.topology.topological_structures
import valuations 
import valuation_spectrum

namespace valuation

/- although strictly speaking the commented-out defintion her
   is a "correct" definition, note that it is
   not constant across equivalence classes of valuations! The "correct" notion of
   continuity for an arbitrary equivalence class of valuations is that the induced
   valuation taking values in the value group is continuous.

   def BAD_is_continuous {R : Type} [comm_ring R] [topological_space R] [topological_ring R] 
  {α : Type} [linear_ordered_comm_group α] (f : R → option α) (Hf : is_valuation f) :
  Prop := ∀ x : α, is_open {r : R | f r < x}

-/    


def is_continuous_aux {R : Type} [comm_ring R] [topological_space R] [topological_ring R] 
  {α : Type} [linear_ordered_comm_group α] {f : R → option α} (Hf : is_valuation f) :
  Prop := ∀ x : α, x ∈ is_valuation.value_group f → is_open {r : R | f r < x}

-- incomplete -- needs Wedhorn 1.25/1.27 
def is_continuous {R : Type} [comm_ring R] [topological_space R] [topological_ring R] 
  : Spv R → Prop := sorry
  
/-
quotient.lift (λ v : valuations R,is_continuous_aux v.Hf) 
  (λ (v w : Spv R) H,begin
    dsimp,
    apply propext,
    split,
    { intro Hv,
      intro b,
      sorry
    },
    sorry
  end)
-/

def Cont (R : Type) [comm_ring R] [topological_space R] [topological_ring R]
  := {vs : Spv R // is_continuous vs}

end valuation