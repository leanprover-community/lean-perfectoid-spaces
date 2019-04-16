import for_mathlib.uniform_space.ring
import for_mathlib.uniform_space.uniform_embedding

noncomputable theory

set_option class.instance_max_depth 200

open ring_completion filter

local attribute [instance] topological_add_group.to_uniform_space topological_add_group_is_uniform

local notation `𝓝` x:70 := nhds x

variables {K : Type*} [discrete_field K] [topological_space K] [topological_ring K]

/-- Zero is not adherent to F -/
def zero_not_adh (F : filter $ units K) : Prop := comap units.val 𝓝 0 ⊓ F = ⊥

variables (K) [separated K]

instance : topological_space (units K) := topological_space.induced units.val (by apply_instance)

local notation `hat` K := ring_completion K

instance help_tc_search : uniform_space (hat K) := ring_completion.uniform_space K

def hat_star := {x : hat K // x ≠ 0}

instance : topological_space (hat_star K) := subtype.topological_space

def coe_units : units K → hat_star K :=
λ x, ⟨x.val, λ h, units.ne_zero x $ (uniform_embedding_coe K).1 h⟩

class completable_top_field [separated K]:=
(nice : ∀ F : filter (units K), cauchy_of units.val F → zero_not_adh F →
  cauchy_of units.val (map (λ x, x⁻¹) F) ∧ zero_not_adh (map (λ x, x⁻¹) F))

lemma de_coe_units : dense_embedding (coe_units K) :=
sorry

lemma de_units_val : dense_embedding (units.val : units K → K) := sorry

lemma continuous_extend_inv [completable_top_field K]: continuous ((de_coe_units K).extend (λ x, x⁻¹)) :=
begin
  --have := continuous_extend_of_really_wants_to _ _ _ _ _ _ _ _ (λ x : units K, x⁻¹),
  --(de_coe_units K),
  sorry
end
