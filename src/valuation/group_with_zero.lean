import algebra.group.units

set_option old_structure_cmd true

class group_with_zero (α : Type*)
  extends monoid α, has_inv α, zero_ne_one_class α, mul_zero_class α :=
[has_decidable_eq : decidable_eq α]
(inv_zero : (0 : α)⁻¹ = 0)
(mul_inv_cancel : ∀ a:α, a ≠ 0 → a * a⁻¹ = 1)

attribute [instance] group_with_zero.has_decidable_eq

section group_with_zero
variables {α : Type*} [group_with_zero α]

@[simp] lemma inv_zero' : (0 : α)⁻¹ = 0 := group_with_zero.inv_zero α

@[simp] lemma mul_inv_cancel' (a : α) (h : a ≠ 0) : a * a⁻¹ = 1 :=
group_with_zero.mul_inv_cancel a h

@[simp] lemma mul_inv_cancel_assoc_left (a b : α) (h : b ≠ 0) :
  (a * b) * b⁻¹ = a :=
calc (a * b) * b⁻¹ = a * (b * b⁻¹) : mul_assoc _ _ _
               ... = a             : by simp [h]

@[simp] lemma mul_inv_cancel_assoc_right (a b : α) (h : a ≠ 0) :
  a * (a⁻¹ * b) = b :=
calc a * (a⁻¹ * b) = (a * a⁻¹) * b : (mul_assoc _ _ _).symm
               ... = b             : by simp [h]

lemma inv_ne_zero' (a : α) (h : a ≠ 0) : a⁻¹ ≠ 0 :=
assume a_eq_0, by simpa [a_eq_0] using mul_inv_cancel' a h

@[simp] lemma inv_mul_cancel' (a : α) (h : a ≠ 0) : a⁻¹ * a = 1 :=
calc a⁻¹ * a = (a⁻¹ * a) * a⁻¹ * a⁻¹⁻¹ : by simp [inv_ne_zero' _ h]
         ... = a⁻¹ * a⁻¹⁻¹             : by simp [h]
         ... = 1                       : by simp [inv_ne_zero' _ h]

@[simp] lemma inv_mul_cancel_assoc_left (a b : α) (h : b ≠ 0) :
  (a * b⁻¹) * b = a :=
calc (a * b⁻¹) * b = a * (b⁻¹ * b) : mul_assoc _ _ _
               ... = a             : by simp [h]

@[simp] lemma inv_mul_cancel_assoc_right (a b : α) (h : a ≠ 0) :
  a⁻¹ * (a * b) = b :=
calc a⁻¹ * (a * b) = (a⁻¹ * a) * b : (mul_assoc _ _ _).symm
               ... = b             : by simp [h]

@[simp] lemma inv_inv'' (a : α) : a⁻¹⁻¹ = a :=
if h : a = 0 then by simp [h] else
calc a⁻¹⁻¹ = a * (a⁻¹ * a⁻¹⁻¹) : by simp [h]
       ... = a                 : by simp [inv_ne_zero' _ h]

end group_with_zero

class comm_group_with_zero (α : Type*) extends comm_monoid α, group_with_zero α.

instance discrete_field.to_comm_group_with_zero {α : Type*} [discrete_field α] :
  comm_group_with_zero α :=
{ zero_mul := _,
  mul_zero := _,
  .. ‹discrete_field α› }
