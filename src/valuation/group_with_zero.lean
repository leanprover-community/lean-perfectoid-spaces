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

lemma ne_zero_of_mul_right_eq_one' (a b : α) (h : a * b = 1) : a ≠ 0 :=
assume a_eq_0, zero_ne_one (by simpa [a_eq_0] using h : (0:α) = 1)

lemma ne_zero_of_mul_left_eq_one' (a b : α) (h : a * b = 1) : b ≠ 0 :=
assume b_eq_0, zero_ne_one (by simpa [b_eq_0] using h : (0:α) = 1)

lemma eq_inv_of_mul_right_eq_one' (a b : α) (h : a * b = 1) :
  b = a⁻¹ :=
calc b = a⁻¹ * (a * b) :
        (inv_mul_cancel_assoc_right _ _ $ ne_zero_of_mul_right_eq_one' a b h).symm
   ... = a⁻¹ : by simp [h]

lemma eq_inv_of_mul_left_eq_one' (a b : α) (h : a * b = 1) :
  a = b⁻¹ :=
calc a = (a * b) * b⁻¹ : (mul_inv_cancel_assoc_left _ _ (ne_zero_of_mul_left_eq_one' a b h)).symm
   ... = b⁻¹ : by simp [h]

@[simp] lemma inv_one' : (1 : α)⁻¹ = 1 :=
eq.symm $ eq_inv_of_mul_right_eq_one' _ _ (mul_one 1)

end group_with_zero

namespace group_with_zero
variables {α : Type*} [group_with_zero α]

def mk₀ (a : α) (h : a ≠ 0) : units α :=
{ val := a,
  inv := a⁻¹,
  val_inv := mul_inv_cancel' a h,
  inv_val := inv_mul_cancel' a h }

@[simp] lemma coe_mk₀ (a : α) (h : ¬ a = 0) : (mk₀ a h : α) = a := rfl

@[simp] lemma coe_unit_mul_inv (a : units α) : (a : α) * a⁻¹ = 1 :=
mul_inv_cancel' _ $ ne_zero_of_mul_right_eq_one' _ (a⁻¹ : units α) $ by simp

@[simp] lemma coe_unit_inv_mul (a : units α) : (a⁻¹ : α) * a = 1 :=
inv_mul_cancel' _ $ ne_zero_of_mul_right_eq_one' _ (a⁻¹ : units α) $ by simp

@[simp] lemma coe_inv_unit (a : units α) : ((a⁻¹ : units α) : α) = a⁻¹ :=
eq_inv_of_mul_right_eq_one' _ _ $ by simp

@[simp] lemma unit_ne_zero (a : units α) : (a : α) ≠ 0 :=
assume a_eq_0, zero_ne_one α $
calc 0 = (a : α) * a⁻¹ : by simp [a_eq_0]
   ... = 1 : by simp

lemma mul_eq_zero (a b : α) (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin
  contrapose! h,
  exact unit_ne_zero ((mk₀ a h.1) * (mk₀ b h.2))
end

lemma mul_left_cancel {x : α} (hx : x ≠ 0) {y z : α} (h : x * y = x * z) : y = z :=
calc y = x⁻¹ * (x * y) : by rw inv_mul_cancel_assoc_right _ _ hx
   ... = x⁻¹ * (x * z) : by rw h
   ... = z             : by rw inv_mul_cancel_assoc_right _ _ hx

lemma mul_right_cancel {x : α} (hx : x ≠ 0) {y z : α} (h : y * x = z * x) : y = z :=
calc y = (y * x) * x⁻¹ : by rw mul_inv_cancel_assoc_left _ _ hx
   ... = (z * x) * x⁻¹ : by rw h
   ... = z             : by rw mul_inv_cancel_assoc_left _ _ hx

lemma mul_inv_eq_of_eq_mul {x : α} (hx : x ≠ 0) {y z : α} (h : y = z * x) : y * x⁻¹ = z :=
h.symm ▸ (mul_inv_cancel_assoc_left z x hx)

lemma eq_mul_inv_of_mul_eq {x : α} (hx : x ≠ 0) {y z : α} (h : z * x = y) : z = y * x⁻¹ :=
eq.symm $ mul_inv_eq_of_eq_mul hx h.symm

end group_with_zero

class comm_group_with_zero (α : Type*) extends comm_monoid α, group_with_zero α.

instance discrete_field.to_comm_group_with_zero {α : Type*} [discrete_field α] :
  comm_group_with_zero α :=
{ zero_mul := _,
  mul_zero := _,
  .. ‹discrete_field α› }
