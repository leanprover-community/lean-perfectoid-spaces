import for_mathlib.linear_ordered_comm_group

import valuation.group_with_zero

set_option old_structure_cmd true

class linear_ordered_comm_group_with_zero (α : Type*)
  extends linear_ordered_comm_monoid α, comm_group_with_zero α :=
(zero_le' : ∀ a, (0:α) ≤ a)

namespace with_zero

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

instance units.linear_order : linear_order (units α) :=
linear_order.lift (coe : units α → α) (λ a b, units.ext) infer_instance

instance units.linear_ordered_comm_group : linear_ordered_comm_group (units α) :=
{ mul_le_mul_left := λ a b h c, mul_le_mul_left h _,
  .. units.linear_order α,
  .. (infer_instance : comm_group (units α))}

noncomputable def with_zero_units_equiv : with_zero (units α) ≃ α :=
equiv.symm $ @equiv.of_bijective α (with_zero (units α))
(λ a, if h : a = 0 then 0 else group_with_zero.mk₀ a h)
begin
  split,
  { intros a b, dsimp,
    split_ifs; simp [with_zero.coe_inj, units.ext_iff, *], },
  { intros a, with_zero_cases a,
    { exact ⟨0, dif_pos rfl⟩ },
    { refine ⟨a, _⟩, rw [dif_neg (group_with_zero.unit_ne_zero a)],
      simp [with_zero.coe_inj, units.ext_iff, *] } }
end

variable {α}

@[simp] lemma zero_le {a : α} : 0 ≤ a := zero_le' a

@[simp] lemma le_zero_iff {a : α} : a ≤ 0 ↔ a = 0 :=
⟨λ h, _root_.le_antisymm h zero_le, λ h, h ▸ le_refl _⟩

variables {a b c : α}

lemma le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b :=
by simpa [h] using linear_ordered_structure.mul_le_mul_right hab c⁻¹

lemma le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma mul_inv_le_of_le_mul (h : c ≠ 0) (hab : a ≤ b * c) : a * c⁻¹ ≤ b :=
le_of_le_mul_right h (by simpa [h] using hab)

def with_zero_adj_units {β : Type*} [linear_ordered_comm_group β] (f : β →* units α) :
  with_zero β →* α :=
monoid_hom.mk
(λ x, match x with
| 0 := 0
| some b := f b
end)
(show (f 1 : α) = 1, by { rw f.map_one, refl })
begin
  intros x y, with_zero_cases x y,
  { show (0 : α) = 0 * 0, exact (zero_mul _).symm },
  { show (0 : α) = 0 * _, exact (zero_mul _).symm },
  { show (0 : α) = _ * 0, exact (mul_zero _).symm },
  { show (f (x*y) : α) = f x * f y, rw f.map_mul, refl },
end

open group_with_zero

lemma div_le_div (a b c d : α) (hb : b ≠ 0) (hd : d ≠ 0) :
  a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
begin
  by_cases ha : a = 0,
  { simp [ha] },
  by_cases hc : c = 0,
  { replace hb := inv_ne_zero' _ hb,
    simp [hb, hc, hd], },
  exact (linear_ordered_structure.div_le_div
    (mk₀ a ha) (mk₀ b hb) (mk₀ c hc) (mk₀ d hd)),
end

end linear_ordered_comm_group_with_zero
