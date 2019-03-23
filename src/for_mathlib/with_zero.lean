import algebra.group

def with_zero.map_comp {α : Type*} {β : Type*} {γ : Type*} (f : α → β) (g : β → γ) :
  with_zero.map (g ∘ f) = (with_zero.map) g ∘ (with_zero.map f)
