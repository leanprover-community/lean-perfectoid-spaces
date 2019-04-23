import topology.maps -- some stuff should go here
import topology.opens -- some stuff should go here

class open_embedding {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  (f : α → β) : Prop :=
(Hopen : is_open_map f)
(Hembedding : embedding f)

namespace topological_space

theorem is_open_map_of_open {α : Type*} [topological_space α] {s : set α} (hs : _root_.is_open s) :
  is_open_map (subtype.val : {x // x ∈ s} → α) := begin
  rintros _ ⟨t, ht, rfl⟩, convert is_open_inter _ _ _ ht hs,
  rw set.image_preimage_eq_inter_range,
  congr',
  exact (set.range_coe_subtype s)
end

theorem is_embedding_of_open {α : Type*} [topological_space α] {s : set α} (hs : _root_.is_open s) :
  embedding (subtype.val : {x // x ∈ s} → α) := ⟨subtype.val_injective, rfl⟩

class open_embedding {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  (f : α → β) : Prop :=
(Hopen : is_open_map f)
(Hembedding : embedding f)

namespace open_embedding
-- is this the right order, or is {α : Type*} [topological_space α] {β : Type*} ... better?
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
  [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

-- one is .id, one is _id. Which is "correct"?
lemma id : open_embedding (@id α : α → α) := ⟨is_open_map.id, embedding_id⟩

-- one is .comp, one is _compose. Which is "correct"?
instance comp (f : α → β) (g : β → γ) [hf : open_embedding f] [hg : open_embedding g] :
  open_embedding (g ∘ f) := ⟨is_open_map.comp hf.1 hg.1, embedding_compose hf.2 hg.2⟩

theorem of_open {s : set α} (hs : _root_.is_open s) :
  open_embedding (subtype.val : {x // x ∈ s} → α) :=
⟨is_open_map_of_open hs, is_embedding_of_open hs⟩

-- todo: prod : α → β and γ → δ gives α x γ → β x δ?

end open_embedding

section is_open_map
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  (f : α → β)

def is_open_map.map (h : is_open_map f) : opens α → opens β :=
λ U, ⟨f '' U.1, h U.1 U.2⟩

def opens.map (U : opens α) : opens U → opens α :=
is_open_map.map subtype.val $ is_open_map_of_open U.2

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
