import data.real.nnreal

import for_mathlib.linear_ordered_comm_group

import valuation.group_with_zero

set_option old_structure_cmd true

/-- A linearly ordered commutative group with zero
is a linearly ordered commutative monoid with a zero elements
such that all nonzero elements are invertible.-/
class linear_ordered_comm_group_with_zero (α : Type*)
  extends linear_ordered_comm_monoid α, comm_group_with_zero α :=
(zero_le' : ∀ a, (0:α) ≤ a)

namespace with_zero

/-- Adjoining a zero element to a linearly ordered commutative group
gives a linearly ordered commutative group with zero.-/
instance (α : Type*) [linear_ordered_comm_group α] [decidable_eq α] :
  linear_ordered_comm_group_with_zero (with_zero α) :=
{ zero_le' := λ a, with_zero.zero_le,
  inv_zero := rfl,
  mul_inv_cancel := λ a h, mul_right_inv a h,
  .. (infer_instance : linear_ordered_comm_monoid (with_zero α)),
  .. (infer_instance : has_inv (with_zero α)),
  .. (infer_instance : zero_ne_one_class (with_zero α)),
  .. (infer_instance : mul_zero_class (with_zero α)) }

end with_zero

namespace linear_ordered_comm_group_with_zero
variables (α : Type*) [linear_ordered_comm_group_with_zero α]

/--The units of a linearly ordered commutative group are linearly ordered.-/
instance units.linear_order : linear_order (units α) :=
linear_order.lift (coe : units α → α) units.ext infer_instance

/--The units of a linearly ordered commutative group with zero
form a linearly ordered commutative group.-/
instance units.linear_ordered_comm_group : linear_ordered_comm_group (units α) :=
{ mul_le_mul_left := λ a b h c, mul_le_mul_left h _,
  .. units.linear_order α,
  .. (infer_instance : comm_group (units α))}

end linear_ordered_comm_group_with_zero

namespace linear_ordered_structure
variables {α : Type*} [group_with_zero α]
variables {a b c d : α}

lemma ne_zero_iff_exists : a ≠ 0 ↔ ∃ u : units α, a = u :=
begin
  split,
  { intro h, use [group_with_zero.mk₀ a h], refl },
  { rintro ⟨u, rfl⟩, exact group_with_zero.unit_ne_zero u }
end

end linear_ordered_structure

namespace linear_ordered_structure
variables {α : Type*} [linear_ordered_comm_group_with_zero α]
variables {a b c d : α}

open group_with_zero

local attribute [instance] classical.prop_decidable
local attribute [instance, priority 0] classical.decidable_linear_order

@[simp] lemma zero_le {a : α} : 0 ≤ a :=
linear_ordered_comm_group_with_zero.zero_le' a

@[simp] lemma le_zero_iff : a ≤ 0 ↔ a = 0 :=
⟨λ h, le_antisymm h zero_le, λ h, h ▸ le_refl _⟩

lemma le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b :=
by simpa [h] using linear_ordered_structure.mul_le_mul_right hab c⁻¹

lemma le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma mul_inv_le_of_le_mul (h : c ≠ 0) (hab : a ≤ b * c) : a * c⁻¹ ≤ b :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma div_le_div' (a b c d : α) (hb : b ≠ 0) (hd : d ≠ 0) :
  a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
begin
  by_cases ha : a = 0,
  { simp [ha] },
  by_cases hc : c = 0,
  { replace hb := inv_ne_zero' _ hb,
    simp [hb, hc, hd], },
  exact (div_le_div (mk₀ a ha) (mk₀ b hb) (mk₀ c hc) (mk₀ d hd)),
end

lemma lt_of_mul_lt_mul_left' {a b c : α} (h : a * b < a * c) : b < c :=
begin
  by_cases ha : a = 0, { contrapose! h, simp [ha] },
  by_cases hc : c = 0, { contrapose! h, simp [hc] },
  by_cases hb : b = 0, { contrapose! hc, simpa [hb] using hc },
  exact linear_ordered_structure.lt_of_mul_lt_mul_left (mk₀ a ha) (mk₀ b hb) (mk₀ c hc) h
end

/-- Every linearly ordered commutative group with zero is an ordered commutative monoid.-/
instance : actual_ordered_comm_monoid α :=
{ lt_of_mul_lt_mul_left := λ a b c, lt_of_mul_lt_mul_left',
  .. ‹linear_ordered_comm_group_with_zero α› }

@[move_cast] lemma coe_min (x y : units α) :
  ((min x y : units α) : α) = min (x : α) (y : α) :=
begin
  by_cases h: x ≤ y,
  { simp [min_eq_left, h] },
  { simp [min_eq_right, le_of_not_le h] }
end

lemma ne_zero_of_lt (h : b < a) : a ≠ 0 :=
by { contrapose! h, simp [h] }

@[simp] lemma zero_lt_unit (u : units α) : (0 : α) < u :=
by { have h := group_with_zero.unit_ne_zero u, contrapose! h, simpa using h }

lemma mul_lt_mul' : a < b → c < d → a*c < b*d :=
begin
  intros hab hcd,
  let b' := group_with_zero.mk₀ b (ne_zero_of_lt hab),
  let d' := group_with_zero.mk₀ d (ne_zero_of_lt hcd),
  have hbd : 0 < b * d,
  { have h := group_with_zero.unit_ne_zero (b' * d'), contrapose! h, simpa using h },
  by_cases ha : a = 0,
  { simp [ha, hbd], },
  by_cases hc : c = 0,
  { simp [hc, hbd], },
  let a' := group_with_zero.mk₀ a ha,
  let c' := group_with_zero.mk₀ c hc,
  show a' * c' < b' * d',
  exact linear_ordered_structure.mul_lt_mul hab hcd
end

lemma mul_inv_lt_of_lt_mul' {x y z : α} (h : x < y*z) : x*z⁻¹ < y :=
begin
  by_cases hx : x = 0, { contrapose! h, simp * at *, },
  by_cases hy : y = 0, { contrapose! h, simp [hy] },
  by_cases hz : z = 0, { contrapose! h, simp [hz] },
  change (group_with_zero.mk₀ _ hx) < (group_with_zero.mk₀ _ hy) * (group_with_zero.mk₀ _ hz) at h,
  exact mul_inv_lt_of_lt_mul h
end
.

lemma mul_lt_right' (γ : α) (h : a < b) (hγ : γ ≠ 0) : a*γ < b*γ :=
begin
  have hb : b ≠ 0 := ne_zero_of_lt h,
  by_cases ha : a = 0,
  { by_contra H, simp [ha] at H, tauto, },
  change (group_with_zero.mk₀ _ ha) < (group_with_zero.mk₀ _ hb) at h,
  exact linear_ordered_structure.mul_lt_right (group_with_zero.mk₀ _ hγ) h
end

end linear_ordered_structure

namespace nnreal

/-- The nonnegative real numbers form a linearly ordered commutative group with zero.-/
noncomputable instance : linear_ordered_comm_group_with_zero nnreal :=
{ inv_zero := by simp,
  zero_le' := zero_le,
  mul_le_mul_left := λ a b h c, mul_le_mul (le_refl _) h (zero_le _) (zero_le _),
  mul_inv_cancel := λ a h, mul_inv_cancel h,
  .. (infer_instance : zero_ne_one_class nnreal),
  .. (infer_instance : has_inv nnreal),
  .. (infer_instance : linear_order nnreal),
  .. (infer_instance : comm_semiring nnreal) }

end nnreal




