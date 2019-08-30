import power_bounded Huber_ring.basic data.polynomial

universes u v

-- Notation for the power bounded subring
local postfix `ᵒ` : 66 := power_bounded_subring

open power_bounded

section integral
variables {R : Type u} [comm_ring R] [decidable_eq R]

-- TODO: mathlib has algebra.is_integral or something like that. We might want to use that.

/-- An element r of a ring is integral over a subring if there exists a monic polynomial p
over the subring such that p(r) = 0.-/
def is_integral (S : set R) [is_subring S] (r : R) : Prop :=
∃ f : polynomial ↥S, (f.monic) ∧ f.eval₂ (@subtype.val _ S) r = 0

-- TODO: mathlib has integral closures now. Probably we can use some predicate from there.

def is_integrally_closed (S : set R) [is_subring S] : Prop :=
∀ r : R, (is_integral S r) → r ∈ S

end integral

-- Wedhorn Def 7.14
structure is_ring_of_integral_elements {R : Type u}
  [Huber_ring R] [decidable_eq R] (Rplus : set R) : Prop :=
[is_subring : is_subring Rplus]
(is_open : is_open Rplus)
(is_int_closed : is_integrally_closed Rplus)
(is_power_bounded : Rplus ⊆ Rᵒ)

-- a Huber Ring is an f-adic ring.
/-- A Huber pair consists of a Huber ring and a
so-call ring of integral elements: an integrally closed, power bounded, open subring.
(Huber called such objects “affinoid rings”.) -/
structure Huber_pair :=
(R : Type) -- change this to (Type u) to enable universes
[RHuber : Huber_ring R]
[dec : decidable_eq R]
(Rplus : set R)
(intel : is_ring_of_integral_elements Rplus)

namespace Huber_pair

instance : has_coe_to_sort Huber_pair :=
{ S := Type, coe := Huber_pair.R }

instance (A : Huber_pair) : Huber_ring A := A.RHuber

end Huber_pair

postfix `⁺` : 66 := λ A : Huber_pair, A.Rplus
