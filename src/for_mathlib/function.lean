variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

def function.comp₂ (f : α → β → γ) (g : γ → δ) : α → β → δ := λ x y, g (f x y)

notation g `∘₂` f := function.comp₂ f g

lemma function.uncurry_comp₂ (f : α → β → γ) (g : γ → δ) :
  function.uncurry (g ∘₂ f) = (g ∘ function.uncurry f) :=
funext $ λ ⟨p, q⟩, rfl
