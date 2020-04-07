import data.finset data.set.function tactic
open set
universes u v

-- "PR'ed" means mathlib #2353

example {α : Type} [decidable_eq α] (a x : α) : (a ∈ ({x} : set α)) = (a ∈ ({x} : finset α)) := rfl

-- PR'ed
lemma set.mem_compl_singleton_iff {α : Type*} {a x : α} : x ∈ -({a} : set α) ↔ x ≠ a :=
by simp only [set.mem_singleton_iff, set.mem_compl_eq]

-- PR'ed
lemma set.subset_compl_singleton_iff {α : Type*} {a : α} {s : set α} : s ⊆ -({a} : set α) ↔ a ∉ s :=
by { rw subset_compl_comm, simp }

variables {α : Type*} {β : Type*} (f : α → β)

-- this is in data.set.basic already (probably after the nonempty refactor?)
lemma set.image_nonempty (s : set α) (h : s.nonempty) : (f '' s).nonempty :=
nonempty.image f h

-- this is also in data.set.basic already
@[simp] lemma set.exists_mem_range {α : Type u} {β : Type v} {f : α → β} {P : β → Prop} :
  (∃ b ∈ range f, P b) ↔ ∃ a, P (f a) :=
exists_range_iff

-- PR'ed but called it exists_range_iff' (order of implicit
-- variables slightly different in PR)
@[simp] lemma set.exists_mem_range' {α : Type u} {β : Type v} {f : α → β} {P : β → Prop} :
  (∃ b, b ∈ range f ∧ P b) ↔ ∃ a, P (f a) :=
⟨by rintros ⟨b, ⟨a, rfl⟩, h⟩ ; exact ⟨a, h⟩, λ ⟨a, h⟩, ⟨f a, mem_range_self a, h⟩⟩

/- Seems to exist already...
lemma set.image_inter_subset (s t : set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
by { rintros _ ⟨x, x_in, rfl⟩, exact ⟨mem_image_of_mem f x_in.1, mem_image_of_mem f x_in.2⟩ }
-/

-- not about sets so not PR'ed
def prod.map' {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}
  (f : α₁ → α₂) (g : β₁ → β₂) : α₁ × β₁ → α₂ × β₂ := λ p : α₁ × β₁, ⟨f p.1, g p.2⟩

infix ` ⨯ `:90 := prod.map'
