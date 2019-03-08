import topology.algebra.ring
import ring_theory.subring
import ring_theory.ideal_operations

universe u

variables {A : Type u} [comm_ring A] [topological_space A] [topological_ring A]

open topological_ring

instance subring_has_zero (R : Type u) [comm_ring R] (S : set R) [HS : is_subring S] : has_zero S :=
⟨⟨0, is_add_submonoid.zero_mem S⟩⟩

instance topological_subring (A₀ : set A) [is_subring A₀] : topological_ring A₀ :=
{ continuous_neg := continuous_subtype_mk _ $ continuous_subtype_val.comp $ continuous_neg A,
  continuous_add := continuous_subtype_mk _ $ continuous_add
    (continuous_fst.comp continuous_subtype_val)
    (continuous_snd.comp continuous_subtype_val),
  continuous_mul := continuous_subtype_mk _ $ continuous_mul
    (continuous_fst.comp continuous_subtype_val)
    (continuous_snd.comp continuous_subtype_val) }

def is_ideal_adic (J : ideal A) : Prop :=
(∀ n : ℕ, is_open (J^n : ideal A).carrier) ∧ (∀ S : set A, (0 : A) ∈ S → is_open S → ∃ n : ℕ, (J^n : ideal A).carrier ⊆ S)

notation `is-`J`-adic` := is_ideal_adic J

def is_adic (A₀ : set A) [is_subring A₀] : Prop := ∃ (J : ideal A₀),
(by haveI := topological_subring A₀; exact is-J-adic)
