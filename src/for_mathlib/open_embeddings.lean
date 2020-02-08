import topology.maps -- some stuff should go here
import topology.opens -- some stuff should go here

namespace topological_space


section is_open_map
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  (f : α → β)

def is_open_map.map (h : is_open_map f) : opens α → opens β :=
λ U, ⟨f '' U.1, h U.1 U.2⟩

def opens.map (U : opens α) : opens U → opens α :=
is_open_map.map subtype.val $ (is_open.open_embedding_subtype_val  U.2).is_open_map

def opens.map_mono {U : opens α} {V W : opens U} (HVW : V ⊆ W) : opens.map U V ⊆ opens.map U W :=
λ x h, set.image_subset _ HVW h

def opens.map_mem_of_mem {U : opens α} {V : opens U} {x : U} (h : x ∈ V) : x.1 ∈ opens.map U V :=
begin
  rcases x with ⟨v, hv⟩,
  use v,
    exact hv,
  exact ⟨h, rfl⟩
end


end is_open_map

end topological_space
