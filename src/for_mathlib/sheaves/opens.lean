/-
  Basic definitions and lemmas about opens.

  TODO : Not use opens as sets when possible.

  Author: Ramon Fernandez Mir
-/

import topology.basic
import topology.opens

universes u v

open topological_space lattice lattice.lattice

section opens

variables {α : Type u} [topological_space α]

-- A couple of useful tricks to work avoid using the lattice jargon when
-- dealing with opens.

@[simp] lemma opens.inter (U V : opens α) :
U ∩ V = ⟨U.1 ∩ V.1, is_open_inter U.2 V.2⟩ := rfl

prefix `⋃` := supr

-- Opens constants.

def opens.univ : opens α := ⟨set.univ, is_open_univ⟩

def opens.empty : opens α := ⟨∅, is_open_empty⟩

-- Some useful lemmas. Maybe versions of them are already somewhere.

lemma opens_supr_mem {γ : Type*} (X : γ → opens α)
: ∀ i x, x ∈ (X i).val → x ∈ (⋃ X).val :=
λ i x Hx, let Xi := X i in
begin
    unfold supr; simp,
    exact ⟨Xi.1, ⟨⟨Xi.2, i, by simp⟩, Hx⟩⟩,
end

lemma opens_supr_subset {γ : Type*} (X : γ → opens α)
: ∀ i, X i ⊆ ⋃ X :=
λ i x, opens_supr_mem X i x

-- Opens comap.

section opens_comap

variables {β : Type v} [topological_space β]
variables {f : α → β} (Hf : continuous f)

@[reducible] def opens.comap : opens β → opens α :=
λ U, ⟨f ⁻¹' U.1, Hf U.1 U.2⟩

def opens.comap_mono (U V : opens β) (HUV : U ≤ V) : opens.comap Hf U ≤ opens.comap Hf V :=
set.preimage_mono HUV

end opens_comap

-- Opens map (assuming that f is an open immersion).

section opens_map

variables {β : Type v} [topological_space β]
variables {f : α → β} (Hf : ∀ (U : opens α), is_open (f '' U))

def opens.map : opens α → opens β :=
λ U, ⟨f '' U, Hf U⟩

lemma opens.map_mono (U V : opens α) (HUV : U ≤ V) : opens.map Hf U ≤ opens.map Hf V :=
set.image_subset f HUV

end opens_map

end opens
