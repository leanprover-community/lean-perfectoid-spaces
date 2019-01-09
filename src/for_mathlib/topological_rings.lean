import analysis.topology.topological_structures
import ring_theory.subring
import ring_theory.ideal_operations

universe u

variables {A : Type u} [comm_ring A] [topological_space A] [topological_ring A]

instance subring_has_zero (R : Type u) [comm_ring R] (S : set R) [HS : is_subring S] : has_zero S :=
⟨⟨0, is_add_submonoid.zero_mem S⟩⟩

instance topological_subring (A₀ : set A) [is_subring A₀] : topological_ring A₀ :=
{ continuous_neg := sorry,
  continuous_add := sorry,
  continuous_mul := sorry
}

def is_ideal_adic (J : ideal A) : Prop :=
(∀ n : ℕ, is_open (J^n : ideal A).carrier) ∧ (∀ S : set A, (0 : A) ∈ S → is_open S → ∃ n : ℕ, (J^n : ideal A).carrier ⊆ S)

notation `is-`J`-adic` := is_ideal_adic J

def is_adic (A₀ : set A) [is_subring A₀] : Prop := ∃ (J : ideal A₀),
(by haveI := topological_subring A₀; exact is-J-adic)
