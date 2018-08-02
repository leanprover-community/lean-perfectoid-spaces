import order.filter

namespace filter
variables {α : Type*} {β : Type*} {γ : Type*}

lemma tendsto_map'_iff {f : β → γ} {g : α → β} {x : filter α} {y : filter γ} :
  tendsto f (map g x) y ↔ tendsto (f ∘ g) x y :=
by rw [tendsto, tendsto, map_map]

end filter