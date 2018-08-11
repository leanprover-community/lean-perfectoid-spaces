import ring_theory.ideals

universe u

theorem is_proper_ideal.one_not_mem {α : Type*} [comm_ring α] {S : set α} [is_proper_ideal S] : (1:α) ∉ S :=
λ h, is_proper_ideal.ne_univ S $ is_submodule.univ_of_one_mem S h

section pow_ideal

variables {α : Type u} [comm_ring α] (S T T₁ T₂ : set α)
variables [is_ideal S]

def mul_ideal (T₁ T₂ : set α) : set α :=
span { x | ∃ y z, y ∈ T₁ ∧ z ∈ T₂ ∧ x = y * z}

def pow_ideal : ℕ → set α
| 0 := set.univ
| (n+1) := mul_ideal (pow_ideal n) T

instance pow_ideal.is_ideal (n : ℕ) : is_ideal (pow_ideal S n) :=
nat.cases_on n (@is_ideal.mk _ _ _ $ is_submodule.univ) $ λ n,
span.is_ideal _

end pow_ideal
