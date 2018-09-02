import data.set.basic

variables {α : Type*} {β : Type*} {γ : Type*}
variables {U : set α} {V : set β}

namespace set
lemma mem_prod' {a : α} {b : β} (a_in : a ∈ U) (b_in : b ∈ V) : (a, b) ∈ set.prod U V :=
⟨a_in, b_in⟩

--lemma prod_sub_preimage_iff {W : set γ} {f : α × β → γ} :
--set.prod U V ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ U → b ∈ V → f (a, b) ∈ W :=
--⟨λ h a b a_in b_in, h (mem_prod' a_in b_in),
-- λ h p p_in, by have := h p.1 p.2 p_in.1 p_in.2 ; rwa prod.mk.eta at this⟩
end set