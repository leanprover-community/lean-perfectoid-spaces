-- rational open data completion stuff.

-- In this file we show that r_o_d_completion r := A<T/s>
-- satisfies the property that if v in D(T1,s1) ⊂ D(T2,s2) then
-- the maps A<Ti/si> - > K_v-hat commute with the restriction map.

-- We then, assuming D(T,s) are a basis for Spa(A), show that
-- we can get maps O_X(U) -> K_v-hat for an arbitrary open with v ∈ U.
-- we need this for the valuations on the stalks.

import valuation.localization_Huber
import for_mathlib.sheaves.stalk_of_rings -- for defining valuations on stalks
--import valuation.field -- where KB just dumped valuation_on_completion

variable {A : Huber_pair}

open topological_space valuation Spv spa

namespace spa.r_o_d_completion

section scary_uniform_space_instance

set_option class.instance_max_depth 100

noncomputable def uniform_space' (v : spa A) : uniform_space (valuation_field (out (v.val))) :=
topological_add_group.to_uniform_space _

local attribute [instance] uniform_space'

instance (v : spa A) : uniform_add_group (valuation_field (out (v.val))) :=
topological_add_group_is_uniform

noncomputable def to_complete_valuation_field {r : rational_open_data A} {v : spa A}
  (hv : v ∈ r.rational_open) :
  r_o_d_completion r → ring_completion (valuation_field (Spv.out v.1)) :=
ring_completion.map (Huber_pair.rational_open_data.to_valuation_field hv)

example {r : rational_open_data A} {v : spa A} (hv : v ∈ r.rational_open) :
  is_ring_hom (Huber_pair.rational_open_data.to_valuation_field hv) := by apply_instance

example {r : rational_open_data A} {v : spa A} (hv : v ∈ r.rational_open) :
  is_ring_hom (Huber_pair.rational_open_data.to_valuation_field hv) := by apply_instance

instance {r : rational_open_data A} {v : spa A} (hv : v ∈ r.rational_open) :
  is_ring_hom (to_complete_valuation_field hv) :=
ring_completion.map_is_ring_hom (rational_open_data.localization r) (valuation_field (Spv.out v.1))
  (Huber_pair.rational_open_data.to_valuation_field_cts hv)

-- next we need to show that the completed maps to K_v-hat all commute with the
-- restriction maps
/-- the maps from rationals opens to completions commute with allowable restriction maps-/
theorem to_valuation_field_commutes {r1 r2 : spa.rational_open_data A} {v : spa A}
  (hv1 : v ∈ r1.rational_open) (hv2 : v ∈ r2.rational_open) (h : r1 ≤ r2) :
(to_complete_valuation_field hv1) = (to_complete_valuation_field hv2) ∘
  (r_o_d_completion.restriction h) :=
begin
  delta to_complete_valuation_field,
  delta r_o_d_completion.restriction,
  let uc1 : uniform_continuous (rational_open_data.localization_map h) :=
  localization_map_is_uniform_continuous h,
  let uc2 : continuous (Huber_pair.rational_open_data.to_valuation_field hv2) :=
    Huber_pair.rational_open_data.to_valuation_field_cts hv2,
  rw Huber_pair.rational_open_data.to_valuation_field_commutes hv1 hv2 h,
  -- is the noncompleted commute.
  convert ring_completion.map_comp uc1 _,
  apply uniform_continuous_of_continuous uc2,
end

end scary_uniform_space_instance

end spa.r_o_d_completion

-- Now we need to show that for any O_X(U) with v in U we have a map
-- to K_v-hat. We do this under the additional assumption that D(T,s) is a basis.
-- First let's write a noncomputable function which gets a basis element.

-- def rational_basis (A : Huber_pair) : set (set (spa A)) :=
-- {U : set (spa A) | ∃ r : rational_open_data A, U = r.rational_open }

lemma spa.exists_rational_open_subset {v : spa A} {U : opens (spa A)} (hv : v ∈ U) :
  ∃ r : rational_open_data_subsets U, v ∈ r.1.rational_open :=
begin
  suffices : U.1 ∈ nhds v,
    rw mem_nhds_of_is_topological_basis (rational_basis.is_basis A) at this,
    rcases this with ⟨_, ⟨r, rfl⟩, hv, hr⟩,
    use ⟨r, hr⟩,
    exact hv,
  apply mem_nhds_sets U.2 hv,
end

noncomputable def spa.rational_open_subset_nhd {v : spa A} {U : opens (spa A)} (hv : v ∈ U) :
  rational_open_data_subsets U :=
classical.some $ spa.exists_rational_open_subset hv

def spa.mem_rational_open_subset_nhd {v : spa A} {U : opens (spa A)} (hv : v ∈ U) :
  v ∈ (spa.rational_open_subset_nhd hv).1.rational_open :=
classical.some_spec $ spa.exists_rational_open_subset hv

namespace spa.presheaf

section scary_uniform_space_instance

set_option class.instance_max_depth 100

noncomputable def uniform_space' (v : spa A) : uniform_space (valuation_field (out (v.val))) :=
topological_add_group.to_uniform_space _

local attribute [instance] uniform_space'

/-- The map from F(U) to K_v for v ∈ U -/
noncomputable def to_valuation_field_completion {v : spa A} {U : opens (spa A)} (hv : v ∈ U)
  (f : spa.presheaf_value U) : ring_completion (valuation_field (Spv.out v.1)) :=
spa.r_o_d_completion.to_complete_valuation_field (spa.mem_rational_open_subset_nhd hv) $
  f.1 $ spa.rational_open_subset_nhd hv

instance {v : spa A}
  {U : opens (spa A)} (hv : v ∈ U) :
  is_ring_hom (to_valuation_field_completion hv) := begin
  delta to_valuation_field_completion,
  let F := (λ (f : presheaf_value U),
       spa.r_o_d_completion.to_complete_valuation_field (spa.mem_rational_open_subset_nhd hv)
       (f.val (spa.rational_open_subset_nhd hv))),
  show is_ring_hom F,
  have H : F =
    ((spa.r_o_d_completion.to_complete_valuation_field (spa.mem_rational_open_subset_nhd hv))
    ∘ (λ (f : presheaf_value U), (f.val (spa.rational_open_subset_nhd hv)))),
    refl,
  rw H,
  refine is_ring_hom.comp _ _,
end

end scary_uniform_space_instance

-- I need now to prove that if V ⊆ U then to_valuation_field_completion commutes with res

-- before we even start with this terrifying noncomputable spa.rational_open_subset_nhd
-- let's check that spa.r_o_d_completion.to_complete_valuation_field commutes with ≤
lemma to_valuation_field_completion_well_defined_aux₁ {v : spa A} {U : opens (spa A)} (hv : v ∈ U)
  (f : spa.presheaf_value U) {r1 r2 : rational_open_data_subsets U}
  (h1 : v ∈ r1.1.rational_open) (h2 : v ∈ r2.1.rational_open) :
spa.r_o_d_completion.to_complete_valuation_field h1 (f.1 r1) =
  spa.r_o_d_completion.to_complete_valuation_field (begin
    show v ∈ (rational_open_data.inter r1.1 r2.1).rational_open,
    rw rational_open_data.rational_open_data_inter,
    exact ⟨h1, h2⟩
  end)
  (f.1 (rational_open_data_subsets_inter r1 r2)) :=
begin
  rw spa.r_o_d_completion.to_valuation_field_commutes h1 _
    (rational_open_data.rational_open_data_le_inter_left r1.1 r2.1),
    swap,
    rw rational_open_data.rational_open_data_inter,
    exact ⟨h1, h2⟩,
  unfold function.comp,
  congr' 1,
  -- exact times out here; convert closes the goal really quickly
  convert f.2 r1 (rational_open_data_subsets_inter r1 r2) _,
end

-- now the other way
lemma to_valuation_field_completion_well_defined_aux₂ {v : spa A} {U : opens (spa A)} (hv : v ∈ U)
  (f : spa.presheaf_value U) {r1 r2 : rational_open_data_subsets U}
  (h1 : v ∈ r1.1.rational_open) (h2 : v ∈ r2.1.rational_open) :
spa.r_o_d_completion.to_complete_valuation_field h2 (f.1 r2) =
  spa.r_o_d_completion.to_complete_valuation_field (begin
    show v ∈ (rational_open_data.inter r1.1 r2.1).rational_open,
    rw rational_open_data.rational_open_data_inter,
    exact ⟨h1, h2⟩
  end)
  (f.1 (rational_open_data_subsets_inter r1 r2)) :=
begin
  rw spa.r_o_d_completion.to_valuation_field_commutes h2 _
    (rational_open_data.rational_open_data_le_inter_right r1.1 r2.1),
    swap,
    rw rational_open_data.rational_open_data_inter,
    exact ⟨h1, h2⟩,
  unfold function.comp,
  congr' 1,
  -- exact times out here; convert closes the goal really quickly
  convert f.2 r2 (rational_open_data_subsets_inter r1 r2) _,
end

-- now let's check it agrees on any rational_open_data_subsets
lemma to_valuation_field_completion_well_defined_aux₃ {v : spa A} {U : opens (spa A)} (hv : v ∈ U)
  (f : spa.presheaf_value U) {r1 r2 : rational_open_data_subsets U}
  (h1 : v ∈ r1.1.rational_open) (h2 : v ∈ r2.1.rational_open) :
  spa.r_o_d_completion.to_complete_valuation_field h1 (f.1 r1) =
  spa.r_o_d_completion.to_complete_valuation_field h2 (f.1 r2) :=
begin
  rw to_valuation_field_completion_well_defined_aux₁ hv f h1 h2,
  rw to_valuation_field_completion_well_defined_aux₂ hv f h1 h2,
end

-- next I will prove that for every r : rational_open_data_subsets U with v ∈ r.1.rational_open,
-- f gets sent to the same thing.
lemma to_valuation_field_completion_well_defined {v : spa A} {U : opens (spa A)} (hv : v ∈ U)
  (f : spa.presheaf_value U) (r : rational_open_data_subsets U) (hr : v ∈ r.1.rational_open):
to_valuation_field_completion hv f =
  spa.r_o_d_completion.to_complete_valuation_field hr (f.1 r) :=
to_valuation_field_completion_well_defined_aux₃ hv f _ hr

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
    ⟨rUV1, begin rw rational_open_data.rational_open_data_inter,
    exact set.subset.trans (set.inter_subset_left _ _) rU.2 end⟩
    ( begin rw rational_open_data.rational_open_data_inter,
        split,
          exact spa.mem_rational_open_subset_nhd hv,
        exact spa.mem_rational_open_subset_nhd _,
      end),
  rw to_valuation_field_completion_well_defined (hUV hv) f
    ⟨rUV1,
      begin rw rational_open_data.rational_open_data_inter,
        exact set.subset.trans (set.inter_subset_right _ _) rV.2
      end⟩
    ( begin
        rw rational_open_data.rational_open_data_inter,
        split,
          exact spa.mem_rational_open_subset_nhd hv,
        exact spa.mem_rational_open_subset_nhd _,
      end),
  refl,
end

end spa.presheaf
