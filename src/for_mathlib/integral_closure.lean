
import ring_theory.integral_closure

variables (R : Type*) (A : Type*) [decidable_eq R] [decidable_eq A]
variables [comm_ring R] [comm_ring A] [algebra R A]

open function

/--An R-algebra A is integrally closed if every element of A that is integral over R is contained in
the image of the canonical map R → A. This algebra_map is required to be injective.-/
structure is_integrally_closed : Prop :=
(inj : injective (algebra_map A : R → A))
(closed : ∀ a : A, (is_integral R a) → a ∈ set.range (algebra_map A : R → A))
