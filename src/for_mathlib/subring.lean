import for_mathlib.add_subgroup group_theory.submonoid

open group

variables {R : Type} [ring R]

/-- `S` is a subgroup: a set containing 1 and closed under multiplication, addition and and additive inverse. -/
class is_subring  (S : set R) extends is_add_subgroup S, is_submonoid S : Prop.

instance subtype.ring {S : set R} [is_subring S] : ring S :=
{ add_comm := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  .. subtype.add_group,
  .. subtype.monoid }