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
  Hid := λ U, by {funext x, cases x, refl},
  Hcomp := λ U V W _ _, rfl,
  Fring := λ x, punit.comm_ring,
  res_is_ring_hom := λ U V _, { map_one := rfl,
  map_mul := λ  _ _, rfl,
  map_add := λ _ _, rfl},
  Ftop := λ U, by apply_instance,
  Ftop_ring := λ U, by apply_instance,
  res_continuous := λ U V _, continuous_of_discrete_topology},
  locality := begin sorry end,
  gluing := sorry,
  homeo := sorry },
  complete := λ U, {complete := sorry},
  valuation := by rintro ⟨⟩,
  local_stalks := by rintro ⟨⟩,
  supp_maximal := by rintro ⟨⟩ }

example : PerfectoidSpace ⟨37, by norm_num⟩ := ⟨empty_CLVRS, by rintro ⟨⟩⟩
