-- rational open data completion stuff.

-- morphisms to the completed valuation field

-- we need this for the valuations on the stalks.

import valuation.localization_Huber

variable {A : Huber_pair}

open topological_space valuation Spv Spa

noncomputable instance Spa.r_o_d_completion.uniform_space' (v : Spa A) : uniform_space (valuation_field (out (v.val))) :=
topological_add_group.to_uniform_space _

instance (v : Spa A) : uniform_add_group (valuation_field (out (v.val))) := topological_add_group_is_uniform

noncomputable def to_complete_valuation_field {r : rational_open_data A} {v : Spa A} (hv : v ∈ r.rational_open) :
r_o_d_completion r → ring_completion (valuation_field (Spv.out v.1)) :=
ring_completion.map (Huber_pair.rational_open_data.to_valuation_field hv)

-- next we need to show that the completed maps to K_v-hat all commute with the
-- restriction maps

theorem to_valuation_field_commutes {r1 r2 : Spa.rational_open_data A} {v : Spa A}
  (hv1 : v ∈ r1.rational_open) (hv2 : v ∈ r2.rational_open) (h : r1 ≤ r2) :
(to_complete_valuation_field hv1) = (to_complete_valuation_field hv2) ∘
  (r_o_d_completion.restriction h) :=
begin
  delta to_complete_valuation_field,
  delta r_o_d_completion.restriction,
  let uc1 : uniform_continuous (rational_open_data.localization_map h) := localization_map_is_uniform_continuous h,
  let uc2 : continuous (Huber_pair.rational_open_data.to_valuation_field hv2) :=
    Huber_pair.rational_open_data.to_valuation_field_cts hv2,
  rw Huber_pair.rational_open_data.to_valuation_field_commutes hv1 hv2 h, -- is the noncompleted commute.
  convert ring_completion.map_comp uc1 _,
  apply uniform_continuous_of_continuous uc2,

end
-- to_valuation_field_commutes r1 r2 h hv1.2 hv2.2

-- Now we need to show that for any O_X(U) with v in U we have a map
-- to K_v-hat. We do this under the additional assumption that D(T,s)
