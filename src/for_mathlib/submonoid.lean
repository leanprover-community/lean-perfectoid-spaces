import group_theory.submonoid

section
variables {α : Type*} [monoid α]

@[to_additive is_add_submonoid.inter]
lemma is_submonoid.inter (s₁ s₂ : set α) [is_submonoid s₁] [is_submonoid s₂] :
  is_submonoid (s₁ ∩ s₂) :=
{ one_mem := ⟨is_submonoid.one_mem _, is_submonoid.one_mem _⟩,
  mul_mem := λ x y hx hy,
    ⟨is_submonoid.mul_mem hx.1 hy.1, is_submonoid.mul_mem hx.2 hy.2⟩ }

end
