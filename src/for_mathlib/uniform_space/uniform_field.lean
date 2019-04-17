import for_mathlib.uniform_space.ring
import for_mathlib.topological_field
import for_mathlib.uniform_space.uniform_embedding

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

set_option class.instance_max_depth 200

open set ring_completion filter

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

instance : zero_ne_one_class (hat K) :=
{ zero_ne_one := assume h, zero_ne_one $ (uniform_embedding_coe K).1 h,
  ..ring_completion.comm_ring K }

def coe_units : units K → hat_star K :=
λ x, ⟨x.val, λ h, units.ne_zero x $ (uniform_embedding_coe K).1 h⟩

class completable_top_field [separated K]:=
(nice : ∀ F : filter (units K), cauchy_of units.val F → zero_not_adh F →
  cauchy_of units.val (map (λ x, x⁻¹) F) ∧ zero_not_adh (map (λ x, x⁻¹) F))

lemma de_units_val : dense_embedding (units.val : units K → K) :=
sorry

lemma de_hat_star : dense_embedding (subtype.val : hat_star K → hat K) :=
sorry

lemma de_coe_units : dense_embedding (coe_units K : units K → hat_star K) :=
sorry

lemma range_units_val : range (units.val : units K → K) = -{0} :=
sorry

lemma range_units_hat_star : range (subtype.val : hat_star K → hat K) = -{0} :=
sorry

def inv_hat_star : hat_star K → hat_star K := (de_coe_units K).extend $ coe_units K ∘ (λ x, x⁻¹)

lemma continuous_inv_hat_star [completable_top_field K]: continuous (inv_hat_star K) :=
begin
  let dkX := de_coe_units K, -- dense embedding K* → hat K*
  let diX := de_units_val K, -- dense embedding K* → K
  let ue := uniform_embedding_coe K, -- uniform embedding K → hat K
  let diY := de_hat_star K, -- dense embedding hat K* → hat K

  have comm : subtype.val ∘ coe_units K = coe ∘ units.val, by { ext, refl },
  apply continuous_extend_of_really_wants_to (λ x : units K, x⁻¹) comm comm
    diX dkX diY diX dkX diY ue ue,
  { rw [range_units_val K, range_units_hat_star K, preimage_compl, compl_subset_compl,
       singleton_subset_iff], simp, refl },
  { rw [range_units_val K, range_units_hat_star K, compl_compl, compl_compl,
        singleton_subset_iff],
    use 0,
    simp,
    refl },
  { intros F cauchyF hF,
    have zero_non_unit : (0 : K) ∉ range (units.val : units K → K),
    { rw range_units_val K, simp },
    have non_unit_zero : ∀ (x : K), x ∉ set.range (units.val : units K → K) → x = 0,
    { rw range_units_val K, simp },
    cases completable_top_field.nice F cauchyF (hF (0 : K) zero_non_unit) with h₁ h₂,
    refine ⟨h₁, _⟩,
    intros x hx,
    rwa non_unit_zero x hx },
end

lemma inv_hat_is_inv : ∀ x : hat_star K, x.val*(inv_hat_star K x).val = 1 :=
sorry

/-- homeomorphim between non-zero elements of hat K and units of hat K -/
def hat_star_is_units : hat_star K ≃ₜ units (hat K) :=
{ to_fun := λ x, ⟨x.val, (inv_hat_star K x).val,
      inv_hat_is_inv K x, mul_comm x.val (inv_hat_star K x).val ▸ (inv_hat_is_inv K x)⟩ ,
  inv_fun := λ x, ⟨x.val, assume h,
                          have (0 : hat K) = 1 := zero_mul x.inv ▸ (h ▸ x.val_inv),
                          zero_ne_one this⟩,
  left_inv := λ x, by simp,
  right_inv := λ x, units.ext rfl,
  continuous_to_fun := continuous_induced_rng continuous_induced_dom,
  continuous_inv_fun := continuous_induced_rng continuous_induced_dom }

local notation `ψ` := (hat_star_is_units K).to_equiv.to_fun
local notation `ψ⁻¹` := (hat_star_is_units K).to_equiv.inv_fun

def hat_inv (x : hat K) : hat K := if h : x = 0 then 0 else
subtype.val (inv_hat_star K ⟨x , h⟩)

lemma invinv : (λ (a : units (hat K)), a⁻¹) = ψ ∘ (inv_hat_star K) ∘ ψ⁻¹ :=
sorry

variables (K)

lemma hat_inv_zero : hat_inv _ (0 : hat K) = (0 : hat K) :=
by simp [hat_inv]

instance hat_has_inv : has_inv (hat K) := ⟨hat_inv K⟩

lemma hat_mul_inv : ∀ a : hat K, a ≠ 0 → a * a⁻¹ = 1 :=
sorry

example : topological_space (units $ hat K) := by apply_instance
instance : discrete_field (hat K) :=
{ inv := hat_inv K,
  zero_ne_one := assume h, discrete_field.zero_ne_one K ((uniform_embedding_coe K).1 h),
  mul_inv_cancel := hat_mul_inv K,
  inv_mul_cancel := by {intro, rw mul_comm, apply hat_mul_inv },
  inv_zero := hat_inv_zero K,
  has_decidable_eq := by apply_instance,
  ..(by apply_instance : comm_ring (hat K)) }

-- Unfortunately, the above instance loose TC search when it comes to finding a topology on
-- units (hat K)
-- TODO: investigate this issue
instance help_tcs : topological_space (units $ hat K) := topological_ring.units_topological_space _

instance [completable_top_field K] : topological_division_ring (hat K) :=
{ continuous_inv :=
    begin
      rw invinv K,
      exact (hat_star_is_units K).continuous_inv_fun.comp (
        (continuous_inv_hat_star K).comp (hat_star_is_units K).continuous_to_fun)
    end,
  ..ring_completion.topological_ring K }
