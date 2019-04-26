import data.set.basic
open set

variables {α : Type*} {β : Type*} (P : set (α × β)) (s : set α) (t : set β)

lemma set.prod_subset_iff :
  (set.prod s t ⊆ P) ↔ ∀ (x : α) (y : β), x ∈ s → y ∈ t → (⟨x, y⟩ : α × β) ∈ P :=
begin
  split ; intro h,
  { intros x y xin yin,
    exact h (mk_mem_prod xin yin),
     },
  { intros p pin,
    cases mem_prod.1 pin with hs ht,
    simpa using h _ _ hs ht },
end
