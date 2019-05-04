import data.set.basic
open set

variables {α : Type*} {β : Type*} (P : set (α × β)) (s : set α) (t : set β)

-- PR'd as #980
lemma set.prod_subset_iff :
  (set.prod s t ⊆ P) ↔ ∀ (x ∈ s) (y ∈ t), (⟨x, y⟩ : α × β) ∈ P :=
⟨λ h _ xin _ yin, h (mk_mem_prod xin yin),
 λ h _ pin, by { cases mem_prod.1 pin with hs ht, simpa using h _ hs _ ht }⟩
