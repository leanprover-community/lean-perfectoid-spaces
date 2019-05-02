-- definitions of adic_space, preadic_space, Huber_pair etc
import topology.algebra.group
import adic_space
import Tate_ring
import power_bounded
import for_mathlib.topological_groups -- for the predicate is_complete_hausdorff

universe u

-- notation for the power bounded subring
local postfix `ᵒ` : 66 := power_bounded_subring

open nat.Prime power_bounded_subring topological_space
variable [nat.Prime] -- fix a prime p

/-- A perfectoid ring, following Fontaine Sem Bourb-/
structure perfectoid_ring (R : Type u) [Huber_ring R] extends Tate_ring R : Prop :=
(complete : is_complete_hausdorff R)
(uniform  : is_uniform R)
(ramified : ∃ ϖ : pseudo_uniformizer R, (ϖ^p : Rᵒ) ∣ p)
(Frob     : ∀ a : Rᵒ, ∃ b : Rᵒ, (p : Rᵒ) ∣ (b^p - a : Rᵒ))

-- 𝒞 is a category whose objects are topological spaces with a presheaf of topological rings and
-- and an equivalence class of valuation on each stalk; a perfectoid space is locally
-- isomorphic to Spa(A) with A a perfectoid ring, and the isomorphism can be checked in 𝒞.

structure perfectoid_space (X : Type u) [topological_space X] extends adic_space X :=
(perfectoid_cover : ∀ x : X, ∃ (U : opens X) (A : Huber_pair) [perfectoid_ring A],
  (x ∈ U) ∧ (𝒞.Spa A) ≅_𝒞 (locally_ringed_valued_space.to_𝒞.restrict U))

def PerfectoidSpace :=
{X : CVLRS.{u} // ∀ x : X, ∃ (U : opens X) (A : Huber_pair.{u}) [perfectoid_ring A],
  (x ∈ U) ∧ nonempty (Spa' A ≅ U)}
