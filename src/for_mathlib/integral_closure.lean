
import ring_theory.integral_closure

variables {R : Type*} [comm_ring R] [decidable_eq R]

/--A subring S of a ring R is integrally closed
if it contains all elements of R that are integral over S.-/
def is_integrally_closed (S : set R) [is_subring S] : Prop :=
∀ r : R, (is_integral S r) → r ∈ S
