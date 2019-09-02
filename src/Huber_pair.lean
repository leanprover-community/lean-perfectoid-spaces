import for_mathlib.integral_closure

import power_bounded Huber_ring.basic

/-!
# Huber pairs

This short file defines Huber pairs.

A Huber pair consists of a Huber ring and a
so-call ring of integral elements: an integrally closed, power bounded, open subring.
A typical example is ℤ_p ⊆ ℚ_p. (However, this example is hard to use as is,
because our fomalisation uses subrings and Lean's version of ℤ_p is not a subring of ℚ_p.
This could be fixed by using injective ring homomorphisms instead of subrings.)

-/

universes u v

-- Notation for the power bounded subring
local postfix `ᵒ` : 66 := power_bounded_subring

open power_bounded

/- An subring of a Huber ring is called a “ring of integral elements”
if it is open, integrally closed, and power bounded. See [Wedhorn, Def 7.14].-/
structure is_ring_of_integral_elements {R : Type u}
  [Huber_ring R] [decidable_eq R] (Rplus : set R) : Prop :=
[is_subring : is_subring Rplus]
(is_open : is_open Rplus)
(is_int_closed : is_integrally_closed Rplus)
(is_power_bounded : Rplus ⊆ Rᵒ)

/-- A Huber pair consists of a Huber ring and a
so-call ring of integral elements: an integrally closed, power bounded, open subring.
(The name “Huber pair” was introduced by Scholze.
Before that, they were called “affinoid rings”.) See [Wedhorn, Def 7.14].-/
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
