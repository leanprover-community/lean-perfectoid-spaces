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

@[priority 1] instance (α : Type*) : has_mem (with_zero α) (set α) :=
⟨λ a s,
match a with
| (some a) := a ∈ s
| none := false
end⟩

def is_valuation : is_valuation (to_fun v H) ↔ (v.characteristic_group ⊆ H ∧ is_convex H) :=
begin
  split; intro h,
  { split,
    { apply group.closure_subset,
      by_contradiction hH,
      rw set.not_subset at hH,
      rcases hH with ⟨γ, ⟨h₁, ⟨r, hr⟩⟩, h₂⟩,
      have hr_add_one : v.canonical_valuation (r+1) ∉ H,
      apply @with_zero.coe_ne_zero H 1,
      },
    { } },
  {  }
end

end horizontal_specialization

end valuation
