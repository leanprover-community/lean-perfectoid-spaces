-- definitions of adic_space, preadic_space, Huber_pair etc
import topology.algebra.group
import adic_space
import Tate_ring
import power_bounded
import for_mathlib.topological_groups -- for the predicate is_complete_hausdorff

-- notation for the power bounded subring
local postfix `ᵒ` : 66 := power_bounded_subring

open nat.Prime power_bounded_subring topological_space
variable [nat.Prime] -- fix a prime p

/-- A perfectoid ring, following Fontaine Sem Bourb-/
structure perfectoid_ring (R : Type) [Huber_ring R] extends Tate_ring R : Prop :=
(complete : is_complete_hausdorff R)
(uniform  : is_uniform R)
(ramified : ∃ ϖ : pseudo_uniformizer R, (ϖ^p : Rᵒ) ∣ p)
(Frob     : ∀ a : Rᵒ, ∃ b : Rᵒ, (p : Rᵒ) ∣ (b^p - a : Rᵒ))

-- CVLRS ("complete valued locally ringed space")
-- is a category whose objects are topological spaces with a presheaf of topological rings
-- and an equivalence class of valuation on each stalk; a perfectoid space is locally
-- isomorphic to Spa(A) with A a perfectoid ring, and the isomorphism can be checked in CVLRS.

namespace CVLRS

/-- Condition for an object of CVLRS to be perfectoid: every point should have an open
neighbourhood isomorphic to Spa(A) for some perfectoid ring A.-/
def is_perfectoid (X : CVLRS) : Prop :=
∀ x : X, ∃ (U : opens X) (A : Huber_pair) [perfectoid_ring A],
  (x ∈ U) ∧ nonempty (Spa' A ≅ U)

end CVLRS

def PerfectoidSpace := {X : CVLRS // X.is_perfectoid}

namespace PerfectoidSpace
open category_theory

instance : large_category PerfectoidSpace := category_theory.full_subcategory _

def to_AdicSpace (X : PerfectoidSpace) : AdicSpace :=
{ property :=
  begin
    intro x,
    rcases X.property x with ⟨U, A, hA, hx, hU⟩,
    use [U, A, hx, hU]
  end,
  ..X }

end PerfectoidSpace
