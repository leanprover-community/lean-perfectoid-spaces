import data.padics.padic_numbers

import for_mathlib.punit_instances

import perfectoid_space

/-!
# An example of a perfectoid space

In this file we show that the empty space is perfectoid.
Every nonempty example requires a non-trivial amount of mathematical effort.
-/

/-- The structure presheaf on the empty space. -/
def CLVRS.empty_presheaf : presheaf_of_topological_rings empty :=
{ F := λ _, unit,
  res := λ _ _ _ _, (),
  Hid := λ U, by {funext x, cases x, refl},
  Hcomp := λ U V W _ _, rfl,
  Fring := λ x, punit.comm_ring,
  res_is_ring_hom := λ U V _,
  { map_one := rfl,
    map_mul := λ  _ _, rfl,
    map_add := λ _ _, rfl },
  Ftop := λ U, by apply_instance,
  Ftop_ring := λ U, by apply_instance,
  res_continuous := λ U V _, continuous_of_discrete_topology }

/-- The structure sheaf on the empty space. -/
def CLVRS.empty_sheaf : sheaf_of_topological_rings empty :=
{ F := CLVRS.empty_presheaf,
  locality := by {rintro _ _ ⟨s⟩ ⟨t⟩ _, refl},
  gluing := by {intros _ _ c _, use (), intro i, cases c i, refl},
  homeo :=
  begin
    rintros ⟨U, HU⟩ ⟨γ, Uis, _⟩ c d,
    dsimp at *,
    change set unit at c,
    rcases subset_subsingleton c with rfl|rfl,
    { convert is_open_empty,
      exact set.image_empty _ },
    { convert is_open_univ,
      apply set.image_univ_of_surjective,
      rintro ⟨s, hs⟩,
      use (),
      apply subtype.eq,
      funext i,
      show () = s i,
      apply subsingleton.elim, },
  end }

/--The empty CLVRS-/
def CLVRS.empty : CLVRS := {
  space := empty,
  sheaf' := CLVRS.empty_sheaf,
  complete := λ U,
  { complete := λ f hf,
    begin
      use (),
      rintro V HV,
      convert f.univ_sets,
      funext x,
      cases x,
      show _ = true, rw eq_true,
      exact mem_of_nhds HV,
    end },
  valuation := by rintro ⟨⟩,
  local_stalks := by rintro ⟨⟩,
  supp_maximal := by rintro ⟨⟩ }

example : PerfectoidSpace ⟨37, by norm_num⟩ := ⟨CLVRS.empty, by rintro ⟨⟩⟩


#sanity_check
#doc_blame


