-- Examples of perfectoid spaces.

import topology.algebra.uniform_group

import perfectoid_space
import algebra.punit_instances
import data.padics.padic_numbers

instance : topological_add_monoid unit :=
  { continuous_add := continuous_of_discrete_topology}

instance : topological_ring unit :=
{ continuous_neg := continuous_of_discrete_topology }

def empty_CLVRS : CLVRS := {
  space := empty,
  top := ⊤,
  sheaf := { F := { F := λ _, unit,
  res := λ _ _ _ _, (),
  Hid := sorry,
  Hcomp := sorry,
  Fring := λ x, punit.comm_ring,
  res_is_ring_hom := sorry,
  Ftop := λ U, by apply_instance,
  Ftop_ring := λ U, by apply_instance,
  res_continuous := sorry },
  locality := sorry,
  gluing := sorry,
  homeo := sorry },
  complete := λ U, {complete := sorry},
  valuation := by rintro ⟨⟩,
  local_stalks := by rintro ⟨⟩,
  supp_maximal := by rintro ⟨⟩ }
