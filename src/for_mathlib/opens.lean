import topology.opens
import logic.basic

namespace topological_space
variables {X : Type*} [topological_space X]


def morphism_on_objects_aux {U : opens X} : opens U → set X :=
λ V, {x : X | x ∈ U ∧ Π (h : x ∈ U), (⟨x, h⟩ : U) ∈ V}

def morphism_on_objects_proof (U : opens X) (V : opens U) :
_root_.is_open (morphism_on_objects_aux V) :=
begin
  rcases V with ⟨_, V, HV, rfl⟩,
  convert HV,
  ext,
  unfold morphism_on_objects_aux,
  dsimp,
  sorry
end


end topological_space
