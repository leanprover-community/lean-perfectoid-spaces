import power_bounded Huber_ring

universes u v

--notation
local postfix `ᵒ` : 66 := power_bounded_subring

open power_bounded

section integral
variables {R : Type u} [comm_ring R] [decidable_eq R]

instance subtype.val.is_ring_hom (S : set R) [is_subring S] : is_ring_hom (@subtype.val _ S) :=
by apply_instance

def is_integral (S : set R) [is_subring S] (r : R) : Prop :=
∃ f : polynomial ↥S, (f.monic) ∧ f.eval₂ (@subtype.val _ S) r = 0

def is_integrally_closed (S : set R) [is_subring S] : Prop :=
∀ r : R, (is_integral S r) → r ∈ S

end integral

-- Wedhorn Def 7.14
structure is_ring_of_integral_elements {R : Type u} [Huber_ring R] [decidable_eq R] (Rplus : set R) : Prop :=
[is_subring : is_subring Rplus]
(is_open : is_open Rplus)
(is_int_closed : is_integrally_closed Rplus)
(is_power_bounded : Rplus ⊆ Rᵒ)

-- a Huber Ring is an f-adic ring.
-- a Huber Pair is what Huber called an Affinoid Ring.
structure Huber_pair :=
(R : Type u)
[RHuber : Huber_ring R]
[dec : decidable_eq R]
(Rplus : set R)
[intel : is_ring_of_integral_elements Rplus]

instance : has_coe_to_sort Huber_pair :=
{ S := Type, coe := Huber_pair.R}

instance Huber_pair.Huber_ring (A : Huber_pair) : Huber_ring A.R := A.RHuber

postfix `⁺` : 66 := λ R : Huber_pair _, R.Rplus
