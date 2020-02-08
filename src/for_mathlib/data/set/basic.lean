import data.finset
open set
universes u v

lemma set.mem_compl_singleton_iff {α : Type*} {a x : α} : x ∈ -({a} : set α) ↔ x ≠ a :=
by simp only [set.mem_singleton_iff, set.mem_compl_eq]

lemma set.subset_compl_singleton_iff {α : Type*} {a : α} {s : set α} : s ⊆ -({a} : set α) ↔ a ∉ s :=
by { rw subset_compl_comm, simp }

variables {α : Type*} {β : Type*} (f : α → β)

lemma set.image_nonempty (s : set α) (h : s.nonempty) : (f '' s).nonempty :=
⟨f h.some, mem_image_of_mem _ h.some_mem⟩

@[simp] lemma set.exists_mem_range {α : Type u} {β : Type v} {f : α → β} {P : β → Prop} :
  (∃ b ∈ range f, P b) ↔ ∃ a, P (f a) :=
⟨by rintros ⟨b, ⟨a, rfl⟩, h⟩ ; exact ⟨a, h⟩, λ ⟨a, h⟩, ⟨f a, mem_range_self a, h⟩⟩

@[simp] lemma set.exists_mem_range' {α : Type u} {β : Type v} {f : α → β} {P : β → Prop} :
  (∃ b, b ∈ range f ∧ P b) ↔ ∃ a, P (f a) :=
⟨by rintros ⟨b, ⟨a, rfl⟩, h⟩ ; exact ⟨a, h⟩, λ ⟨a, h⟩, ⟨f a, mem_range_self a, h⟩⟩

lemma set.image_inter_subset (s t : set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by { rintros _ ⟨x, x_in, rfl⟩, exact ⟨mem_image_of_mem f x_in.1, mem_image_of_mem f x_in.2⟩ }


def prod.map' {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}
  (f : α₁ → α₂) (g : β₁ → β₂) : α₁ × β₁ → α₂ × β₂ := λ p : α₁ × β₁, ⟨f p.1, g p.2⟩

infix ` ⨯ `:90 := prod.map'
