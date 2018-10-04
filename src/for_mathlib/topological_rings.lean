import analysis.topology.topological_structures
import ring_theory.subring
import for_mathlib.ideals

universe u

variables {A : Type u} [comm_ring A] [topological_space A] [topological_ring A]

instance subring_has_zero (R : Type u) [comm_ring R] (S : set R) [HS : is_subring S] : has_zero S :=
⟨⟨0, is_add_submonoid.zero_mem S⟩⟩

instance topological_subring (A₀ : set A) [is_subring A₀] : topological_ring A₀ :=
{ continuous_neg := sorry,
  continuous_add := sorry,
  continuous_mul := sorry
}

def is_ideal_adic (J : set A) [is_ideal J] : Prop :=
(∀ n, is_open (pow_ideal J n)) ∧ (∀ S : set A, (0 : A) ∈ S → is_open S → ∃ n, pow_ideal J n ⊆ S)

notation `is-`J`-adic` := is_ideal_adic J

def is_adic (A₀ : set A) [is_subring A₀] : Prop := ∃ (J : set A₀) [hJ : is_ideal J],
(by haveI := topological_subring A₀; haveI := hJ; exact is-J-adic)
