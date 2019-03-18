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

-- this is all in PR 810

variables {α : Type*} [monoid α] {s : set α}
variables {β : Type*} [add_monoid β] {t : set β}

lemma powers.one_mem {x : α} : (1 : α) ∈ powers x := ⟨0,pow_zero _⟩

lemma multiples.zero_mem {x : β} : (0 : β) ∈ multiples x := ⟨0,add_monoid.zero_smul _⟩

lemma powers.self_mem {x : α} : x ∈ powers x := ⟨1,pow_one _⟩

lemma multiples.self_mem {x : β} : x ∈ multiples x := ⟨1,add_monoid.one_smul _⟩

namespace monoid

theorem closure_singleton {x : α} : closure ({x} : set α) = powers x :=
set.eq_of_subset_of_subset (closure_subset $ set.singleton_subset_iff.2 $ powers.self_mem) $
  is_submonoid.power_subset $ set.singleton_subset_iff.1 $ subset_closure

end monoid
