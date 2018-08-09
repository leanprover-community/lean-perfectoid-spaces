import order.filter

import for_mathlib.data.set.basic

namespace filter
variables {α : Type*} {β : Type*} {γ : Type*}

lemma tendsto_map'_iff {f : β → γ} {g : α → β} {x : filter α} {y : filter γ} :
  tendsto f (map g x) y ↔ tendsto (f ∘ g) x y :=
by rw [tendsto, tendsto, map_map]

lemma tendsto_prod_iff {f : α × β → γ} {x : filter α} {y : filter β} {z : filter γ} :
 filter.tendsto f (filter.prod x y) z 
 ↔ ∀ W ∈ z.sets, ∃ U ∈ x.sets,  ∃ V ∈ y.sets, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W :=
by simp [tendsto_def, mem_prod_iff, set.prod_sub_preimage_iff]

lemma tendsto_prod_self_iff {f : α × α → β} {x : filter α} {y : filter β} :
 filter.tendsto f (filter.prod x x) y 
 ↔ ∀ W ∈ y.sets, ∃ U ∈ x.sets, ∀ (x x' : α), x ∈ U → x' ∈ U → f (x, x') ∈ W :=
by simp [tendsto_def, mem_prod_same_iff, set.prod_sub_preimage_iff]
end filter