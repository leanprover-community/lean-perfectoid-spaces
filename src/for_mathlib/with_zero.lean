import data.equiv.basic
import group_theory.subgroup

universes u v


section
open tactic interactive (parse loc.wildcard) interactive.types (location) lean.parser (many ident)

run_cmd mk_simp_attr `with_zero_simp

meta def tactic.with_zero_cases : list expr → tactic unit
| (h::t) := seq (induction h [] (some `with_zero.cases_on) >> skip) $ tactic.with_zero_cases t
| [] := do try (interactive.norm_cast loc.wildcard),
           try (tactic.interactive.simp_core {} assumption ff [] [`with_zero_simp] loc.wildcard),
           try (do exfalso, assumption)

/-- Case bashing for with_zero. If `x₁, ... x_n` have type `with_zero α` then
`with_zero cases x₁ ... x_n` will split according to whether each `x_i` is zero or coerced from
`α` then run `norm_cast at *`, try to simplify using the simp rules `with_zero_simp`, and try to
get a contradiction. -/
meta def tactic.interactive.with_zero_cases (l : parse $ many ident) :=
l.mmap tactic.get_local >>= tactic.with_zero_cases
end

namespace with_zero


variables {α : Type u} {β : Type v}

@[simp, with_zero_simp] lemma zero_le [preorder α] {x : with_zero α} : 0 ≤ x :=
by { intros y hy, cases hy }

@[simp, with_zero_simp] lemma zero_lt_coe [preorder α] {a : α} : (0 : with_zero α) < a :=
⟨a, rfl, λ y hy, by cases hy⟩


@[simp, with_zero_simp] lemma not_coe_eq_zero [preorder α] {x : α} : ¬ (x : with_zero α) = 0 :=
λ h, option.no_confusion h

@[elim_cast] lemma coe_le_coe [preorder α] {x y : α} :
  (x : with_zero α) ≤ (y : with_zero α) ↔ x ≤ y :=
⟨λ h, by rcases (h x rfl) with ⟨z, ⟨h2⟩, h3⟩; exact h3, λ _ _ h, ⟨y, rfl, by cases h ; assumption⟩⟩

@[elim_cast] lemma coe_lt_coe [preorder α] {x y : α} :
  (x : with_zero α) < (y : with_zero α) ↔ x < y :=
by repeat { rw [lt_iff_le_not_le, coe_le_coe] }

-- TODO: replace `coe_one` in mathlib by this one, which seems to be stated as needed by norm_cast.
-- Same remark applies to the next two lemmas.
@[elim_cast] lemma coe_one' [has_one α] : (1 : with_zero α) = ((1 : α) : with_zero α) := rfl

@[move_cast] lemma inv_coe' {α : Type*} [has_inv α] (a : α) :
 ((a⁻¹ : α) : with_zero α) = (a : with_zero α)⁻¹  := rfl

@[move_cast] lemma mul_coe' {α : Type*} [has_mul α] (a b : α) :
  ((a * b : α) : with_zero α) = (a : with_zero α) * b := rfl

attribute [elim_cast] coe_inj

@[simp] lemma le_zero_iff_eq_zero [preorder α] {x : with_zero α} : x ≤ 0 ↔ x = 0 :=
begin
  with_zero_cases x,
  intro h,
  rcases h x rfl with ⟨_, h, _⟩,
  exact option.no_confusion h,
end

@[simp] lemma not_coe_le_zero [preorder α] (x : α) : ¬ (x : with_zero α) ≤ 0 :=
begin
  intro h,
  rw le_zero_iff_eq_zero at h,
  exact not_coe_eq_zero h,
end

@[simp] lemma not_lt_zero [preorder α] (x : with_zero α) : ¬ x < 0 :=
begin
  intro h,
  with_zero_cases x,
  exact lt_irrefl _ h,
  exact not_coe_le_zero x (le_of_lt h),
end

@[simp] lemma map_zero {f : α → β} : map f 0 = 0 := option.map_none'

@[simp, elim_cast] lemma map_coe {f : α → β} {a : α} : map f (a : with_zero α) = f a :=
option.map_some'

@[simp] lemma map_id {α : Type*} : map (id : α → α) = id := option.map_id

lemma map_comp {α β γ : Type*} (f : α → β) (g : β → γ) (r : with_zero α) :
  map (g ∘ f) r = map g (map f r) :=
by cases r; refl

@[simp] lemma map_eq_zero_iff {f : α → β} {a : with_zero α} : map f a = 0 ↔ a = 0 :=
⟨λ h, by with_zero_cases a, λ h, by simp [h]⟩

lemma injective_map {f : α → β} (H : function.injective f) :
function.injective (map f) := option.injective_map H

lemma map_monotone [preorder α] [preorder β] {f : α → β} (H : monotone f) :
  monotone (map f) :=
λ x y, by { with_zero_cases x y, exact λ h, H h }

lemma map_strict_mono [linear_order α] [partial_order β] {f : α → β}
  (H : ∀ a b, a < b → f a < f b) :
  strict_mono (map f) :=
λ x y, by { with_zero_cases x y, exact λ h, H _ _ h }

lemma map_le [preorder α] [preorder β] {f : α → β}
  (H : ∀ a b : α, a ≤ b ↔ f a ≤ f b) (x y : with_zero α) :
x ≤ y ↔ map f x ≤ map f y :=
by { with_zero_cases x y, exact H x y }

@[move_cast] lemma coe_min (x y : α) [decidable_linear_order α] :
  ((min x y : α) : with_zero α) = min x y :=
begin
  by_cases h: x ≤ y,
  { simp [min_eq_left, h] },
  { simp [min_eq_right, le_of_not_le h] }
end

section group
variables [group α]

lemma mul_left_cancel : ∀ {x : with_zero α} (h : x ≠ 0) {y z : with_zero α}, x * y = x * z → y = z
| 0       h := false.elim $ h rfl
| (a : α) h := λ y z h2, begin
  have h3 : (a⁻¹ : with_zero α) * (a * y) = a⁻¹ * (a * z) := by rw h2,
  rwa [←mul_assoc, ←mul_assoc, mul_left_inv _ h, one_mul, one_mul] at h3,
end

lemma mul_right_cancel : ∀ {x : with_zero α} (h : x ≠ 0) {y z : with_zero α}, y * x = z * x → y = z
| 0       h := false.elim $ h rfl
| (a : α) h := λ y z h2, begin
  have h3 : (y * a) * a⁻¹ = (z * a) * a⁻¹ := by rw h2,
  rwa [mul_assoc, mul_assoc, mul_right_inv _ h, mul_one, mul_one] at h3,
end

lemma mul_inv_eq_of_eq_mul : ∀ {x : with_zero α} (h : x ≠ 0) {y z : with_zero α},
  y = z * x → y * x⁻¹ = z
| 0       h := false.elim $ h rfl
| (x : α) h := λ _ _ _, mul_right_cancel h (by rwa [mul_assoc, mul_left_inv _ h, mul_one])

lemma eq_mul_inv_of_mul_eq {x : with_zero α} (h : x ≠ 0) {y z : with_zero α} (h2 : z * x = y) :
  z = y * x⁻¹ := eq.symm $ mul_inv_eq_of_eq_mul h h2.symm

end group

end with_zero
