import valuation.basic
import valuation.canonical
import group_theory.subgroup

universes u u₀ u₁ u₂ u₃ -- v is used for valuations

variables {Γ : Type u} [linear_ordered_comm_group Γ]
variables {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]
variables {Γ₃ : Type u₃} [linear_ordered_comm_group Γ₃]

variables {R : Type u₀} -- This will be a ring, assumed commutative in some sections

namespace valuation
variables [comm_ring R]

def characteristic_group (v : valuation R Γ) : set v.value_group :=
group.closure ({γ | γ ≥ 1 ∧ ∃ r, v.canonical_valuation r = γ})

namespace characteristic_group
variables (v : valuation R Γ)

instance : is_subgroup (v.characteristic_group) := group.closure.is_subgroup _

end characteristic_group

section

variables (v : valuation R Γ) (H : set v.value_group) [is_subgroup H]

instance subgroup_linear_ordered_comm_group : linear_ordered_comm_group H :=
{ to_comm_group := subtype.comm_group,
  mul_le_mul_left :=
  begin

  end }

def horizontal_specialization (v : valuation R Γ) (H : set v.value_group) [is_subgroup H] (h : H ⊆ v.characteristic_group) :
  valuation R H :=
sorry

end

end valuation
