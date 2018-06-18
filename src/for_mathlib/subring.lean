import for_mathlib.add_subgroup group_theory.submonoid
import poly
import algebra.ring
local attribute [instance] classical.prop_decidable

open group

variables {R : Type} [ring R]

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and and additive inverse. -/
class is_subring  (S : set R) extends is_add_subgroup S, is_submonoid S : Prop.

instance subset.ring {S : set R} [is_subring S] : ring S :=
{ add_comm      := assume ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ add_comm _ _,
  left_distrib  := assume ⟨a,_⟩ ⟨b,_⟩ ⟨c,_⟩, subtype.eq $ left_distrib _ _ _,
  right_distrib := assume ⟨a,_⟩ ⟨b,_⟩ ⟨c,_⟩, subtype.eq $ right_distrib _ _ _,
  .. subtype.add_group,
  .. subtype.monoid }

instance subtype.ring {S : set R} [is_subring S] : ring (subtype S) := subset.ring

namespace is_ring_hom

instance {S : set R} [is_subring S] : is_ring_hom (@subtype.val R S) :=
{ map_add := λ _ _, rfl,
  map_mul := λ _ _, rfl,
  map_one := rfl }

end is_ring_hom

variables [decidable_eq R]

def polynomial.map {S : Type} [ring S] (f : S → R) [is_ring_hom f] : polynomial S → polynomial R :=
finsupp.map_range f (is_ring_hom.map_zero f)

def is_integral (S : set R) [is_subring S] (r : R) : Prop :=
∃ f : polynomial S, (polynomial.monic f) ∧ (polynomial.map (@subtype.val R S) f).eval r = 0

def is_integrally_closed (S : set R) [is_subring S] :=
∀ r : R, (is_integral S r) → r ∈ S
