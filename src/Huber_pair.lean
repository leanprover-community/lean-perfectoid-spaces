import power_bounded Huber_ring

universes u v

open power_bounded
variables {cR : Type u} [comm_ring cR] [decidable_eq cR]

def polynomial.map {S : Type v} [comm_ring S] (f : S → cR) [is_ring_hom f] : polynomial S → polynomial cR :=
finsupp.map_range f (is_ring_hom.map_zero f)

def is_integral (S : set cR) [is_subring S] (r : cR) : Prop := 
sorry
--∃ f : polynomial ↥S, (polynomial.monic f) ∧ polynomial.eval r (@polynomial.map cR _ ↥S _ (subtype.val) is_ring_hom.is_ring_hom f) = 0

def is_integrally_closed (S : set cR) [is_subring S] :=
∀ r : cR, (is_integral S r) → r ∈ S

-- Wedhorn Def 7.14
structure is_ring_of_integral_elements {R : Type u} [Huber_ring R] [decidable_eq R] (Rplus : set R) : Prop :=
[is_subring : is_subring Rplus]
(is_open : is_open Rplus)
(is_int_closed : is_integrally_closed Rplus)
(is_power_bounded : Rplus ⊆ { r : R | is_power_bounded r})

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
