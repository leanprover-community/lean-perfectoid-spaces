import r_o_d_completion
import valuation.field

open topological_space valuation Spv spa uniform_space

namespace spa.presheaf

variable {A : Huber_pair}
-- now we can define the valuation on the stalks

local attribute [instance, priority 0] classical.prop_decidable

section scary_uniform_space_instance

set_option class.instance_max_depth 100

local attribute [instance] uniform_space'

noncomputable def stalk_to_valuation_field (x : spa A) :
  stalk_of_rings (spa.presheaf_of_topological_rings A).to_presheaf_of_rings x →
  completion (valuation_field (Spv.out x.1)) :=
to_stalk.rec (spa.presheaf_of_topological_rings A).to_presheaf_of_rings x
  (completion (valuation_field (Spv.out x.1))) (λ U hxU, to_valuation_field_completion hxU)
  (λ U V HUV r hxU, (to_valuation_field_completion_commutes hxU HUV r).symm)

instance is_ring_hom' (x : spa A) :
  is_ring_hom (stalk_to_valuation_field x) := to_stalk.rec_is_ring_hom _ _ _ _ _

noncomputable def stalk_valuation (x : spa A) :
valuation (stalk_of_rings (spa.presheaf_of_topological_rings A).to_presheaf_of_rings x)
  (value_group (out x.1)) :=
valuation.comap (valuation_on_completion (out x.1)) (stalk_to_valuation_field x)


end scary_uniform_space_instance

end spa.presheaf
