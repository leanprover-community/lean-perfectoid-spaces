/-
Perfectoid Spaces

by Kevin Buzzard, Johan Commelin, and Patrick Massot
-/

-- We import definitions of adic_space, preadic_space, Huber_pair etc
import adic_space
import Tate_ring
import power_bounded

-- notation for the power bounded subring
local postfix `ᵒ` : 66 := power_bounded_subring

open power_bounded_subring topological_space

/-- A perfectoid ring, following Fontaine Sem. Bourbaki-/
structure perfectoid_ring (R : Type) [Huber_ring R] (p : ℕ) [is_prime p] extends Tate_ring R : Prop :=
(complete : is_complete_hausdorff R)
(uniform  : is_uniform R)
(ramified : ∃ ϖ : pseudo_uniformizer R, (ϖ^p : Rᵒ) ∣ p)
(Frob     : ∀ a : Rᵒ, ∃ b : Rᵒ, (p : Rᵒ) ∣ (b^p - a : Rᵒ))

-- CLVRS ("complete locally valued ringed space") is a category
-- whose objects are topological spaces with a presheaf of topological rings
-- and an equivalence class of valuation on each stalk; a perfectoid space is locally
-- isomorphic to Spa(A) with A a perfectoid ring, and the isomorphism can be checked in CLVRS.

/-- Condition for an object of CLVRS to be perfectoid: every point should have an open
neighbourhood isomorphic to Spa(A) for some perfectoid ring A.-/
def CLVRS.is_perfectoid (X : CLVRS) (p : ℕ) [is_prime p]: Prop :=
∀ x : X, ∃ (U : opens X) (A : Huber_pair) [perfectoid_ring A p],
  (x ∈ U) ∧ (Spa A ≊ U)

/-- The category of perfectoid spaces.-/
def PerfectoidSpace (p : ℕ) [is_prime p] := {X : CLVRS // X.is_perfectoid p}
