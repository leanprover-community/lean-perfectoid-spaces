import topology.uniform_space.basic
import topology.uniform_space.uniform_embedding

section
open uniform_space
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [uniform_space α] [uniform_space β] [uniform_space γ] [uniform_space δ]

local notation f `∘₂` g := function.bicompr f g

def uniform_continuous₂ (f : α → β → γ) := uniform_continuous (function.uncurry f)

lemma uniform_continuous₂_def (f : α → β → γ) : uniform_continuous₂ f ↔ uniform_continuous (function.uncurry f) := iff.rfl

lemma uniform_continuous₂_curry (f : α × β → γ) : uniform_continuous₂ (function.curry f) ↔ uniform_continuous f :=
by rw  [←function.uncurry_curry f] {occs := occurrences.pos [2]} ; refl

lemma uniform_continuous₂.comp {f : α → β → γ} {g : γ → δ}
  (hg : uniform_continuous g) (hf : uniform_continuous₂ f) :
uniform_continuous₂ (g ∘₂ f) :=
begin
  unfold uniform_continuous₂,
  rw function.uncurry_bicompr,
  exact hg.comp hf
end

lemma uniform_embedding.comp {f : α → β} (hf : uniform_embedding f)
  {g : β → γ} (hg : uniform_embedding g) : uniform_embedding (g ∘ f) :=
⟨function.injective_comp hg.1 hf.1,
 by rw [show (λ (x : α × α), ((g ∘ f) x.1, (g ∘ f) x.2)) =
         (λ y : β × β, (g y.1, g y.2)) ∘ (λ x : α × α, (f x.1, f x.2)), by ext ; simp,
        ← filter.comap_comap_comp, hg.2, hf.2]⟩
end
