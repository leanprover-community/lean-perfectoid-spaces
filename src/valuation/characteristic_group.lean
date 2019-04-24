import valuation.basic
import valuation.canonical
import group_theory.subgroup

local attribute [instance] classical.prop_decidable
noncomputable theory

universes u u₀ -- v is used for valuations

variables {Γ : Type u} [linear_ordered_comm_group Γ]

variables {R : Type u₀} -- This will be a ring, assumed commutative in some sections

namespace valuation
open linear_ordered_comm_group
variables [comm_ring R]

def characteristic_group (v : valuation R Γ) : set v.value_group :=
group.closure ({γ | γ ≥ 1 ∧ ∃ r, v.canonical_valuation r = γ})

namespace characteristic_group
variables (v : valuation R Γ)

instance : is_subgroup (v.characteristic_group) := group.closure.is_subgroup _

end characteristic_group

namespace horizontal_specialization

def to_fun (v : valuation R Γ) (H : set v.value_group) : R → with_zero H :=
option.retract (set_coe_embedding H) ∘ v.canonical_valuation

variables (v : valuation R Γ) (H : set v.value_group) [is_subgroup H]

local attribute [instance] with_zero.has_mem

-- Wedhorn Rmk 4.15
def is_valuation : is_valuation (to_fun v H) ↔ (v.characteristic_group ⊆ H ∧ is_convex H) :=
begin
  split; intro h,
  { split,
    { apply group.closure_subset,
      by_contradiction hH,
      rw set.not_subset at hH,
      rcases hH with ⟨γ, ⟨h₁, ⟨r, hr⟩⟩, h₂⟩,
      replace h₁ : γ > 1,
      { apply lt_of_le_of_ne h₁,
        rintro rfl,
        apply h₂,
        exact is_submonoid.one_mem H },
      have hr_add_one : v.canonical_valuation (r+1) ∉ H,
      { rwa [valuation.map_add_of_distinct_val, max_eq_left_of_lt, hr],
        { rw [valuation.map_one, hr],
          sorry },
        sorry },
      apply @with_zero.coe_ne_zero H 1,
      sorry
      },
    { sorry } },
  { sorry }
end

end horizontal_specialization

end valuation
