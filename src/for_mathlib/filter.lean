import order.filter.basic

open filter set
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-
    f
  α → β
g ↓   ↓ h
  γ → δ
    i
-/
variables {f : α → β} {g : α → γ} {h : β → δ} {i : γ → δ} (H : h ∘ f = i ∘ g)
include H

lemma filter.map_comm (F : filter α) : map h (map f F) = map i (map g F) :=
by rw [filter.map_map, H, ← filter.map_map]

lemma filter.comap_comm (G : filter δ) : comap f (comap h G) = comap g (comap i G) :=
by rw [filter.comap_comap_comp, H, ← filter.comap_comap_comp]
omit H

variables (φ : α → β)

lemma tendsto_pure (F : filter α) (b : β) : tendsto φ F (pure b) ↔ φ ⁻¹' {b} ∈ F :=
tendsto_principal

variables {G : filter β} {s : set α} {t : set β} {φ}

lemma mem_comap_sets_of_inj (h : ∀ a a', φ a = φ a' → a = a') :
  s ∈ comap φ G ↔ ∃ t ∈ G, s = φ ⁻¹' t :=
begin
  rw mem_comap_sets,
  split ; rintros ⟨t, ht, hts⟩,
  { use t ∪ φ '' s,
    split,
    { simp [mem_sets_of_superset ht] },
    { rw [preimage_union, preimage_image_eq _ h],
      exact (union_eq_self_of_subset_left hts).symm } },
  { use [t, ht],
    rwa hts }
end
