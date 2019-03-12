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
class perfectoid_ring (R : Type u) [Huber_ring R] extends Tate_ring R : Prop :=
(complete : is_complete_hausdorff R)
(uniform  : is_uniform R)
(ramified : ∃ ϖ : pseudo_uniformizer R, (ϖ^p : Rᵒ) ∣ p)
(Frob     : ∀ a : Rᵒ, ∃ b : Rᵒ, (p : Rᵒ) ∣ (b^p - a : Rᵒ))

class perfectoid_space (X : Type u) extends adic_space X :=
(perfectoid_cover : ∀ x : X, ∃ (U : opens X) (A : Huber_pair) [perfectoid_ring A.R],
  (x ∈ U) ∧ is_preadic_space_equiv U (Spa A))
