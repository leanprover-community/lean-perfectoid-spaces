import Spa.localization_Huber
import Spa.presheaf
import sheaves.stalk_of_rings

/-!
# The valuation on the stalk

We define the valuations on the stalks of the structure presheaf of the adic spectrum

TODO(jmc): Process these notes by kmb:
In this file we show that rat_open_data_completion r := A<T/s>
satisfies the property that if v in D(T1,s1) ⊂ D(T2,s2) then
the maps A<Ti/si> - > K_v-hat commute with the restriction map.

We then, assuming D(T,s) are a basis for Spa(A), show that
we can get maps O_X(U) -> K_v-hat for an arbitrary open with v ∈ U.
we need this for the valuations on the stalks.

-/

open_locale classical
open topological_space valuation Spv spa uniform_space

variable {A : Huber_pair}

local attribute [instance] valued.uniform_space

namespace spa.rat_open_data_completion

/-- The natural map from A<T/s> to the completion of the valuation field of a valuation v
contained in D(T/s). -/
noncomputable def to_complete_valuation_field {r : rational_open_data A} {v : spa A}
  (hv : v ∈ r.open_set) :
  rat_open_data_completion r → completion (valuation_field (Spv.out v.1)) :=
completion.map (Huber_pair.rational_open_data.to_valuation_field hv)

example {r : rational_open_data A} {v : spa A} (hv : v ∈ r.open_set) :
  is_ring_hom (Huber_pair.rational_open_data.to_valuation_field hv) := by apply_instance

/-- The natural map from A<T/s> to the completion of the valuation field of a valuation v
contained in D(T/s) is a ring homomorphism. -/
instance {r : rational_open_data A} {v : spa A} (hv : v ∈ r.open_set) :
  is_ring_hom (to_complete_valuation_field hv) :=
completion.is_ring_hom_map (Huber_pair.rational_open_data.to_valuation_field_cts hv)

-- next we need to show that the completed maps to K_v-hat all commute with the
-- restriction maps
/-- the maps from rationals opens to completions commute with allowable restriction maps-/
theorem to_valuation_field_commutes {r1 r2 : spa.rational_open_data A} {v : spa A}
  (hv1 : v ∈ r1.open_set) (hv2 : v ∈ r2.open_set) (h : r1 ≤ r2) :
(to_complete_valuation_field hv1) = (to_complete_valuation_field hv2) ∘
  (rat_open_data_completion.restriction h) :=
begin
  delta to_complete_valuation_field,
  delta rat_open_data_completion.restriction,
  have uc1 : uniform_continuous (rational_open_data.localization_map h),
    from rational_open_data.localization_map_is_uniform_continuous h,
  have uc2 : uniform_continuous (Huber_pair.rational_open_data.to_valuation_field hv2),
    from uniform_continuous_of_continuous (Huber_pair.rational_open_data.to_valuation_field_cts hv2),
  rw [Huber_pair.rational_open_data.to_valuation_field_commutes hv1 hv2 h, completion.map_comp uc2 uc1]
end

end spa.rat_open_data_completion

-- Now we need to show that for any 𝒪_X(U) with v in U we have a map to K_v-hat.
-- We do this under the additional assumption that D(T,s) is a basis.
-- First let's write a noncomputable function which gets a basis element.

lemma spa.exists_rational_open_subset {v : spa A} {U : opens (spa A)} (hv : v ∈ U) :
  ∃ r : rational_open_data_subsets U, v ∈ r.1.open_set :=
begin
  suffices : U.1 ∈ nhds v,
  { rw mem_nhds_of_is_topological_basis (rational_basis.is_basis) at this,
    rcases this with ⟨_, ⟨r, rfl⟩, hv, hr⟩,
    use ⟨r, hr⟩,
    exact hv, },
  apply mem_nhds_sets U.2 hv,
end

/-- Given an open set U and a valuation v, this chooses a random rational open subset
containing v and contained in U. -/
noncomputable def spa.rational_open_subset_nhd {v : spa A} {U : opens (spa A)} (hv : v ∈ U) :
  rational_open_data_subsets U :=
classical.some $ spa.exists_rational_open_subset hv

lemma spa.mem_rational_open_subset_nhd {v : spa A} {U : opens (spa A)} (hv : v ∈ U) :
  v ∈ (spa.rational_open_subset_nhd hv).1.open_set :=
classical.some_spec $ spa.exists_rational_open_subset hv

namespace spa.presheaf

/-- The map from F(U) to K_v for v ∈ U, that restricts a section of the structure presheaf
to the completion of the valuation field of v. -/
noncomputable def to_valuation_field_completion {v : spa A} {U : opens (spa A)} (hv : v ∈ U)
  (f : spa.presheaf_value U) : completion (valuation_field (Spv.out v.1)) :=
spa.rat_open_data_completion.to_complete_valuation_field (spa.mem_rational_open_subset_nhd hv) $
  f.1 $ spa.rational_open_subset_nhd hv

/-- Restricting a section of the structure presheaf to a smaller open set is a ring homomorphism.-/
instance restriction_is_ring_hom (U : opens (spa A)) (r : rational_open_data_subsets U) :
  is_ring_hom (λ (f : presheaf_value U), f.val r) :=
{ map_one := rfl,
  map_mul := λ _ _, rfl,
  map_add := λ _ _, rfl }

/-- The map that restricts a section of the structure presheaf above U to the completion of
the valuation field of v ∈ U is a ring homomorphism. -/
instance {v : spa A} {U : opens (spa A)} (hv : v ∈ U) :
  is_ring_hom (to_valuation_field_completion hv) :=
begin
  show is_ring_hom
    ((spa.rat_open_data_completion.to_complete_valuation_field
        (spa.mem_rational_open_subset_nhd hv)) ∘
      (λ (f : presheaf_value U), (f.val (spa.rational_open_subset_nhd hv)))),
  exact is_ring_hom.comp _ _,
end

-- I need now to prove that if V ⊆ U then to_valuation_field_completion commutes with res

-- before we even start with this terrifying noncomputable spa.rational_open_subset_nhd
-- let's check that spa.rat_open_data_completion.to_complete_valuation_field commutes with ≤
lemma to_valuation_field_completion_well_defined_aux₁ {v : spa A} {U : opens (spa A)}
  (f : spa.presheaf_value U) {r1 r2 : rational_open_data_subsets U}
  (h1 : v ∈ r1.1.open_set) (h2 : v ∈ r2.1.open_set) :
spa.rat_open_data_completion.to_complete_valuation_field h1 (f.1 r1) =
  spa.rat_open_data_completion.to_complete_valuation_field (begin
    show v ∈ (r1.1.inter r2.1).open_set,
    rw rational_open_data.inter_open_set,
    exact ⟨h1, h2⟩
  end)
  (f.1 (rational_open_data_subsets_inter r1 r2)) :=
begin
  rw spa.rat_open_data_completion.to_valuation_field_commutes h1 _
    (rational_open_data.le_inter_left r1.1 r2.1),
    swap,
    rw rational_open_data.inter_open_set,
    exact ⟨h1, h2⟩,
  unfold function.comp,
  congr' 1,
  -- exact times out here; convert closes the goal really quickly
  convert f.2 r1 (rational_open_data_subsets_inter r1 r2) _,
end

-- now the other way
lemma to_valuation_field_completion_well_defined_aux₂ {v : spa A} {U : opens (spa A)}
  (f : spa.presheaf_value U) {r1 r2 : rational_open_data_subsets U}
  (h1 : v ∈ r1.1.open_set) (h2 : v ∈ r2.1.open_set) :
spa.rat_open_data_completion.to_complete_valuation_field h2 (f.1 r2) =
  spa.rat_open_data_completion.to_complete_valuation_field (begin
    show v ∈ (rational_open_data.inter r1.1 r2.1).open_set,
    rw rational_open_data.inter_open_set,
    exact ⟨h1, h2⟩
  end)
  (f.1 (rational_open_data_subsets_inter r1 r2)) :=
begin
  rw spa.rat_open_data_completion.to_valuation_field_commutes h2 _
    (rational_open_data.le_inter_right r1.1 r2.1),
    swap,
    rw rational_open_data.inter_open_set,
    exact ⟨h1, h2⟩,
  unfold function.comp,
  congr' 1,
  -- exact times out here; convert closes the goal really quickly
  convert f.2 r2 (rational_open_data_subsets_inter r1 r2) _,
end

-- now let's check it agrees on any rational_open_data_subsets
lemma to_valuation_field_completion_well_defined_aux₃ {v : spa A} {U : opens (spa A)}
  (f : spa.presheaf_value U) {r1 r2 : rational_open_data_subsets U}
  (h1 : v ∈ r1.1.open_set) (h2 : v ∈ r2.1.open_set) :
  spa.rat_open_data_completion.to_complete_valuation_field h1 (f.1 r1) =
  spa.rat_open_data_completion.to_complete_valuation_field h2 (f.1 r2) :=
begin
  rw to_valuation_field_completion_well_defined_aux₁ f h1 h2,
  rw to_valuation_field_completion_well_defined_aux₂ f h1 h2,
end

-- next I will prove that for every r : rational_open_data_subsets U with v ∈ r.1.rational_open,
-- f gets sent to the same thing.
lemma to_valuation_field_completion_well_defined {v : spa A} {U : opens (spa A)} (hv : v ∈ U)
  (f : spa.presheaf_value U) (r : rational_open_data_subsets U) (hr : v ∈ r.1.open_set):
to_valuation_field_completion hv f =
  spa.rat_open_data_completion.to_complete_valuation_field hr (f.1 r) :=
to_valuation_field_completion_well_defined_aux₃ f _ hr

-- now the main goal
/-- If v ∈ U then the map from 𝒪_X(U) to `completion (valuation_field v)`
    commutes with restriction (so we can get a map from the stalk at v) -/
theorem to_valuation_field_completion_commutes {v : spa A} {U V : opens (spa A)} (hv : v ∈ U)
  (hUV : U ⊆ V) (f : spa.presheaf_value V) :
  to_valuation_field_completion (hUV hv) f =
  to_valuation_field_completion hv (spa.presheaf_map hUV f) :=
begin
  -- to_valuation_field_completion involves choosing a random basis element.
  let rU := spa.rational_open_subset_nhd hv,
  let rV := spa.rational_open_subset_nhd (hUV hv),
  -- we now need to intersect these two things.
  let rUV1 := rational_open_data.inter rU.1 rV.1,
  rw to_valuation_field_completion_well_defined hv (spa.presheaf_map hUV f)
    ⟨rUV1, begin rw rational_open_data.inter_open_set,
    exact set.subset.trans (set.inter_subset_left _ _) rU.2 end⟩
    ( begin rw rational_open_data.inter_open_set,
        split,
          exact spa.mem_rational_open_subset_nhd hv,
        exact spa.mem_rational_open_subset_nhd _,
      end),
  rw to_valuation_field_completion_well_defined (hUV hv) f
    ⟨rUV1,
      begin rw rational_open_data.inter_open_set,
        exact set.subset.trans (set.inter_subset_right _ _) rV.2
      end⟩
    ( begin
        rw rational_open_data.inter_open_set,
        split,
          exact spa.mem_rational_open_subset_nhd hv,
        exact spa.mem_rational_open_subset_nhd _,
      end),
  refl,
end

set_option class.instance_max_depth 49

/--An auxiliary function in the definition of the valuations on the stalks
of the structure presheaf of the adic spectrum of a Huber pair:
the valuation is obtained by pulling back a valuation along this function.

It is the natural map from the stalk above a point in spa(A),
which is an equivalence class of valuations,
to the completion of the valuation field of a valuation
that is a representative of this equivalence class. -/
noncomputable def stalk_to_valuation_field (x : spa A) :
  stalk_of_rings (spa.presheaf_of_topological_rings A).to_presheaf_of_rings x →
  completion (valuation_field (Spv.out x.1)) :=
to_stalk.rec (spa.presheaf_of_topological_rings A).to_presheaf_of_rings x
  (completion (valuation_field (Spv.out x.1))) (λ U hxU, to_valuation_field_completion hxU)
  (λ U V HUV r hxU, (to_valuation_field_completion_commutes hxU HUV r).symm)

/-- The natural map from the stalk above a point v in spa(A) to the
completion of the valuation field of v is a ring homomorphism. -/
instance stalk_to_valuation_field.is_ring_hom (x : spa A) :
  is_ring_hom (stalk_to_valuation_field x) := to_stalk.rec_is_ring_hom _ _ _ _ _

/--The valuation on the stalk of the structure presheaf of the adic spectrum.-/
noncomputable def stalk_valuation (x : spa A) :
  valuation (stalk_of_rings (spa.presheaf_of_topological_rings A).to_presheaf_of_rings x)
    (value_monoid (out x.1)) :=
(valuation_on_completion (out x.1)).comap (stalk_to_valuation_field x)

end spa.presheaf
