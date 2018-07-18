import for_mathlib.add_subgroup group_theory.submonoid
-- import poly -- mason-stother doesn't compile at the moment
import algebra.ring
local attribute [instance] classical.prop_decidable

open group

variables {R : Type} [ring R]

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and and additive inverse. -/
class is_subring  (S : set R) extends is_add_subgroup S, is_submonoid S : Prop.

variables {S : set R} [is_subring S]

instance subset.ring : ring S :=
{ add_comm      := assume ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ add_comm _ _,
  left_distrib  := assume ⟨a,_⟩ ⟨b,_⟩ ⟨c,_⟩, subtype.eq $ left_distrib _ _ _,
  right_distrib := assume ⟨a,_⟩ ⟨b,_⟩ ⟨c,_⟩, subtype.eq $ right_distrib _ _ _,
  .. subtype.add_group,
  .. subtype.monoid }

instance subset.comm_ring {R : Type} [comm_ring R] {S : set R} [is_subring S] : comm_ring S :=
{ mul_comm := assume ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ mul_comm _ _,
  .. subset.ring }

instance subtype.ring : ring (subtype S) := subset.ring
instance subtype.comm_ring {R : Type} [comm_ring R] {S : set R} [is_subring S] : comm_ring (subtype S) := subset.comm_ring

namespace is_ring_hom

instance {S : set R} [is_subring S] : is_ring_hom (@subtype.val R S) :=
{ map_add := λ _ _, rfl,
  map_mul := λ _ _, rfl,
  map_one := rfl }

end is_ring_hom

-- variables [decidable_eq R]
-- 
-- def polynomial.map {S : Type} [ring S] (f : S → R) [is_ring_hom f] : polynomial S → polynomial R :=
-- finsupp.map_range f (is_ring_hom.map_zero f)

def is_integral (S : set R) [is_subring S] (r : R) : Prop := sorry
-- ∃ f : polynomial S, (polynomial.monic f) ∧ (polynomial.map (@subtype.val R S) f).eval r = 0

def is_integrally_closed (S : set R) [is_subring S] :=
∀ r : R, (is_integral S r) → r ∈ S
