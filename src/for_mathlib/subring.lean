import for_mathlib.add_subgroup group_theory.submonoid

open group

variables {R : Type} [ring R]

/-- `S` is a subgroup: a set containing 1 and closed under multiplication, addition and and additive inverse. -/
class is_subring  (S : set R) extends is_add_subgroup S, is_submonoid S : Prop.

instance subtype.ring {S : set R} [is_subring S] : ring S :=
{ add_comm      := assume ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ add_comm _ _,
  left_distrib  := assume ⟨a,_⟩ ⟨b,_⟩ ⟨c,_⟩, subtype.eq $ left_distrib _ _ _,
  right_distrib := assume ⟨a,_⟩ ⟨b,_⟩ ⟨c,_⟩, subtype.eq $ right_distrib _ _ _,
  .. subtype.add_group,
  .. subtype.monoid }

instance set.comm_ring [comm_ring R] {S : set R} [is_subring S] : comm_ring S :=
{ mul_comm := sorry, -- assume ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ mul_comm _ _,
  .. subtype.ring }

instance subtype.comm_ring [comm_ring R] {S : set R} [is_subring S] : comm_ring (subtype S) :=
{ mul_comm := sorry, -- assume ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ mul_comm _ _,
  .. subtype.ring }

def is_integral (S : set R) [is_subring S] (r : R) : Prop := sorry
-- ∃ f : (poly S), (is_monic f) ∧ (f(r) = 0)

def is_integrally_closed (S : set R) [is_subring S] :=
∀ r : R, (is_integral S r) → r ∈ S
