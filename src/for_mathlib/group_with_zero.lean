import algebra.group.units
import data.equiv.basic

import for_mathlib.with_zero

set_option old_structure_cmd true

/-- A type `α` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include fields and the ordered monoids that are the
target of valuations in general valuation theory.

Currently division rings are not an example,
because they don't have the requirement 0⁻¹ = 0.-/
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

lemma inv_inj'' {Γ₀ : Type*} [group_with_zero Γ₀] {g h : Γ₀} :
  g⁻¹ = h⁻¹ ↔ g = h :=
begin
  split,
  { intro H,
    by_cases Hg : g = 0,
    { by_cases Hh : h = 0, { rw [Hg, Hh] },
      have := congr_arg ((*) h) H, rw mul_inv_cancel' _ Hh at this,
      replace := eq_inv_of_mul_left_eq_one' _ _ this,
      rw [this, inv_inv''] },
    { have := congr_arg ((*) g) H, rw mul_inv_cancel' _ Hg at this,
      replace := eq_inv_of_mul_left_eq_one' _ _ this.symm,
      rw [this, inv_inv''] } },
  { exact congr_arg _ }
end

end group_with_zero

namespace group_with_zero
variables {α : Type*} [group_with_zero α]

/-- Every nonzero element is a unit.-/
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

instance : no_zero_divisors α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := mul_eq_zero,
  .. (‹_› : group_with_zero α) }

@[simp] lemma mul_eq_zero_iff {a b : α} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
⟨mul_eq_zero a b, by rintro (H|H); simp [H]⟩

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

lemma mul_inv_rev (x y : α) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
begin
  by_cases hx : x = 0, { simp [hx] },
  by_cases hy : y = 0, { simp [hy] },
  symmetry, apply eq_inv_of_mul_left_eq_one', simp [_root_.mul_assoc, hx, hy],
end

lemma pow_eq_zero (x : α) (n : ℕ) (h : x^n = 0) : x = 0 :=
begin
  induction n with n ih, { rw pow_zero at h, exfalso, exact one_ne_zero h },
  by_cases hx : x = 0, { exact hx },
  apply ih,
  replace h := congr_arg ((*) x⁻¹) h,
  rwa [pow_succ, mul_zero, inv_mul_cancel_assoc_right _ _ hx] at h,
end

/--Adjoining a zero element to the units of a group with zero
is naturally equivalent to the group with zero.-/
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

theorem inv_comm_of_comm {a b : α} (H : a * b = b * a) : a⁻¹ * b = b * a⁻¹ :=
begin
  have : a⁻¹ * (b * a) * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ :=
    congr_arg (λ x:α, a⁻¹ * x * a⁻¹) H.symm,
  by_cases h : a = 0, { rw [h, inv_zero', zero_mul, mul_zero] },
  rwa [inv_mul_cancel_assoc_right _ _ h, mul_assoc, mul_inv_cancel_assoc_left _ _ h] at this,
end

section nat_pow

@[simp] theorem inv_pow (a : α) (n : ℕ) : (a⁻¹)^n = (a^n)⁻¹ :=
by induction n with n ih; [exact inv_one'.symm,
  rw [pow_succ', pow_succ, ih, mul_inv_rev]]

-- This should be done for [no_zero_divisors]
lemma eq_zero_of_pow_eq_zero {a : α} {n : ℕ} (h : a^n = 0) : a = 0 :=
begin
  induction n with n ih,
  { exfalso, rw pow_zero at h, exact one_ne_zero h },
  rw [pow_succ, mul_eq_zero_iff] at h,
  cases h; solve_by_elim
end

-- This should be done for [no_zero_divisors]
lemma pow_ne_zero {a : α} {n : ℕ} (h : a ≠ 0) : a^n ≠ 0 :=
assume H, h $ eq_zero_of_pow_eq_zero H

theorem pow_sub (a : α) {m n : ℕ} (ha : a ≠ 0) (h : n ≤ m) : a^(m - n) = a^m * (a^n)⁻¹ :=
have h1 : m - n + n = m, from nat.sub_add_cancel h,
have h2 : a^(m - n) * a^n = a^m, by rw [←pow_add, h1],
eq_mul_inv_of_mul_eq (pow_ne_zero ha) h2

theorem pow_inv_comm (a : α) (m n : ℕ) : (a⁻¹)^m * a^n = a^n * (a⁻¹)^m :=
by rw inv_pow; exact inv_comm_of_comm (pow_mul_comm _ _ _)

end nat_pow

section int_pow
open int

/--
The power operation in a group with zero.
This extends `monoid.pow` to negative integers
with the definition `a^(-n) = (a^n)⁻¹`.
-/
def gpow (a : α) : ℤ → α
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹

@[priority 10] instance : has_pow α ℤ := ⟨gpow⟩

@[simp] theorem gpow_coe_nat (a : α) (n : ℕ) : a ^ (n:ℤ) = a ^ n := rfl

@[simp] theorem gpow_of_nat (a : α) (n : ℕ) : a ^ of_nat n = a ^ n := rfl

@[simp] theorem gpow_neg_succ (a : α) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ := rfl

local attribute [ematch] le_of_lt
open nat

@[simp] theorem gpow_zero (a : α) : a ^ (0:ℤ) = 1 := rfl

@[simp] theorem gpow_one (a : α) : a ^ (1:ℤ) = a := mul_one _

@[simp] theorem one_gpow : ∀ (n : ℤ), (1 : α) ^ n = 1
| (n : ℕ) := one_pow _
| -[1+ n] := show _⁻¹=(1:α), by rw [_root_.one_pow, inv_one']

@[simp] theorem gpow_neg (a : α) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := rfl
| 0       := inv_one'.symm
| -[1+ n] := (inv_inv'' _).symm

theorem gpow_neg_one (x : α) : x ^ (-1:ℤ) = x⁻¹ := congr_arg has_inv.inv $ pow_one x

theorem inv_gpow (a : α) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := inv_pow a n
| -[1+ n] := congr_arg has_inv.inv $ inv_pow a (n+1)

private lemma gpow_add_aux (a : α) (h : a ≠ 0) (m n : nat) :
  a ^ ((of_nat m) + -[1+n]) = a ^ of_nat m * a ^ -[1+n] :=
or.elim (nat.lt_or_ge m (nat.succ n))
 (assume h1 : m < succ n,
  have h2 : m ≤ n, from le_of_lt_succ h1,
  suffices a ^ -[1+ n-m] = a ^ of_nat m * a ^ -[1+n],
    by rwa [of_nat_add_neg_succ_of_nat_of_lt h1],
  show (a ^ nat.succ (n - m))⁻¹ = a ^ of_nat m * a ^ -[1+n],
  by rw [← succ_sub h2, pow_sub _ h (le_of_lt h1), mul_inv_rev, inv_inv'']; refl)
 (assume : m ≥ succ n,
  suffices a ^ (of_nat (m - succ n)) = (a ^ (of_nat m)) * (a ^ -[1+ n]),
    by rw [of_nat_add_neg_succ_of_nat_of_ge]; assumption,
  suffices a ^ (m - succ n) = a ^ m * (a ^ n.succ)⁻¹, from this,
  by rw pow_sub; assumption)

theorem gpow_add (a : α) (h : a ≠ 0) : ∀ (i j : ℤ), a ^ (i + j) = a ^ i * a ^ j
| (of_nat m) (of_nat n) := pow_add _ _ _
| (of_nat m) -[1+n]     := gpow_add_aux _ h _ _
| -[1+m]     (of_nat n) := by rw [add_comm, gpow_add_aux _ h,
  gpow_neg_succ, gpow_of_nat, ← inv_pow, ← pow_inv_comm]
| -[1+m]     -[1+n]     :=
  suffices (a ^ (m + succ (succ n)))⁻¹ = (a ^ m.succ)⁻¹ * (a ^ n.succ)⁻¹, from this,
  by rw [← succ_add_eq_succ_add, add_comm, _root_.pow_add, mul_inv_rev]

theorem gpow_add_one (a : α) (h : a ≠ 0) (i : ℤ) : a ^ (i + 1) = a ^ i * a :=
by rw [gpow_add _ h, gpow_one]

theorem gpow_one_add (a : α) (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [gpow_add _ h, gpow_one]

theorem gpow_mul_comm (a : α) (h : a ≠ 0) (i j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i :=
by rw [← gpow_add _ h, ← gpow_add _ h, add_comm]

theorem gpow_mul (a : α) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
| (m : ℕ) (n : ℕ) := pow_mul _ _ _
| (m : ℕ) -[1+ n] := (gpow_neg _ (m * succ n)).trans $
  show (a ^ (m * succ n))⁻¹ = _, by rw pow_mul; refl
| -[1+ m] (n : ℕ) := (gpow_neg _ (succ m * n)).trans $
  show (a ^ (m.succ * n))⁻¹ = _, by rw [pow_mul, ← inv_pow]; refl
| -[1+ m] -[1+ n] := (pow_mul a (succ m) (succ n)).trans $
  show _ = (_⁻¹^_)⁻¹, by rw [inv_pow, inv_inv'']

theorem gpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
by rw [mul_comm, gpow_mul]

end int_pow

end group_with_zero

/-- A type `α` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
class comm_group_with_zero (α : Type*) extends comm_monoid α, group_with_zero α.

/- TODO(jmc): Refactor the algebraic hierarchy so that
division rings and discrete fields extend group_with_zero (resp. comm_group_with_zero).

Once that is done, unify group_with_zero.mk₀ with units.mk0. -/

/--Every field is a comm_group_with_zero.-/
instance discrete_field.to_comm_group_with_zero {α : Type*} [discrete_field α] :
  comm_group_with_zero α :=
{ zero_mul := _,
  mul_zero := _,
  .. ‹discrete_field α› }
