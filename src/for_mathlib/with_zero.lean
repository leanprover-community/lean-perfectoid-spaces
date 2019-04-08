import data.equiv.basic
import group_theory.subgroup
import for_mathlib.option_inj

universes u v

-- this should be in order.bounded_lattice with with_bot.partial_order
instance {α : Type*} [preorder α] : preorder (with_bot α) :=
{ le          := λ o₁ o₂ : option α, ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b,
  lt          := (<),
  lt_iff_le_not_le := by intros; cases a; cases b;
                         simp [lt_iff_le_not_le];
                         split; try {exact id}; refl,
  le_refl     := λ o a ha, ⟨a, ha, le_refl _⟩,
  le_trans    := λ o₁ o₂ o₃ h₁ h₂ a ha,
    let ⟨b, hb, ab⟩ := h₁ a ha, ⟨c, hc, bc⟩ := h₂ b hb in
    ⟨c, hc, le_trans ab bc⟩,
}

namespace with_zero

instance {α : Type*} [preorder α] : preorder (with_zero α) :=
show preorder (with_bot α), by apply_instance

variables {α : Type u} {β : Type v}

@[simp] theorem zero_le [preorder α] {x : with_zero α} : 0 ≤ x :=
begin
  intros y hy, cases hy
end

@[simp] theorem none_le [preorder α] {x : with_zero α} :
  @has_le.le (with_zero α) _ none x := zero_le

@[simp] theorem none_lt_some [preorder α] {a : α} :
  (0 : with_zero α) < some a :=
begin
  use a, use rfl,
  intros y hy, cases hy,
end

@[simp] theorem zero_lt_some [preorder α] {a : α} :
  @has_lt.lt (with_zero α) _ 0 (some a : with_zero α) := none_lt_some

@[simp] theorem not_some_le_zero [preorder α] {x : α} :
¬ @has_le.le (with_zero α) _ (some x) 0 :=
λ h, by rcases h x rfl with ⟨y, hy, h⟩; cases hy

@[simp] theorem not_some_le_none [preorder α] {x : α} :
¬ @has_le.le (with_zero α) _ (some x) none := not_some_le_zero

@[simp] theorem not_some_eq_zero [preorder α] {x : α} :
¬ (some x : with_zero α) = (0 : with_zero α) := by apply option.no_confusion

@[simp] theorem not_some_eq_none [preorder α] {x : α} :
¬ (some x : with_zero α) = none := by apply option.no_confusion

theorem some_le_some_of_le [preorder α] {x y : α} (h : x ≤ y) :
(x : with_zero α) ≤ y :=
λ a ha, ⟨y, rfl, by cases ha; assumption⟩

@[simp] theorem some_le_some' [preorder α] {x y : α} : (x : with_zero α) ≤ (y : with_zero α) ↔ x ≤ y :=
⟨λ h, by rcases (h x rfl) with ⟨z, ⟨h2⟩, h3⟩; exact h3, some_le_some_of_le⟩

@[simp] theorem some_le_some [preorder α] {x y : α} :
  @has_le.le (with_zero α) _ (some x) (some y) ↔ x ≤ y := some_le_some'

@[simp] theorem le_zero_iff_eq_zero [partial_order α] {x : with_zero α} : x ≤ 0 ↔ x = 0 :=
by cases x; simp; try {refl}; {intro h, exact option.no_confusion h}

def map (f : α → β) : with_zero α → with_zero β := option.map f

@[simp] lemma map_zero {f : α → β} : map f 0 = 0 := option.map_none'
@[simp] lemma map_none {f : α → β} : map f none = 0 := option.map_none'

@[simp] lemma map_some {f : α → β} {a : α} : map f (some a) = some (f a) := option.map_some'

lemma map_id {α : Type*} : map (id : α → α) = id := option.map_id

lemma map_comp {α β γ : Type*} (f : α → β) (g : β → γ) (r : with_zero α) :
  with_zero.map (g ∘ f) r = (with_zero.map g) ((with_zero.map f) r) :=
by cases r; refl

lemma map_eq_zero_iff {f : α → β} {a : with_zero α} : map f a = 0 ↔ a = 0 :=
begin
  split; intro h,
  { cases a, {refl}, rw map_some at h, revert h, exact dec_trivial },
  { rw h, exact map_zero }
end

theorem map_inj {f : α → β} (H : function.injective f) :
function.injective (map f) := option.map_inj H

theorem map_monotone [preorder α] [preorder β] {f : α → β} (H : monotone f) :
  monotone (map f) :=
begin
  intros x y,
  cases x; cases y,
    {simp},
    {simp},
    {simp},
    {simpa using @H _ _}
end

theorem map_strict_mono [linear_order α] [partial_order β] {f : α → β}
  (H : ∀ a b, a < b → f a < f b) :
  ∀ a b, a < b → (map f) a < (map f) b :=
begin
  intros x y,
  cases x; cases y,
  {simp},
  {simp},
  {simp},
  {simpa using H _ _ }
end

theorem map_le [preorder α] [preorder β] {f : α → β}
  (H : ∀ a b : α, a ≤ b ↔ f a ≤ f b) (x y : with_zero α) :
x ≤ y ↔ map f x ≤ map f y :=
begin
  cases x; cases y,
  { convert iff.refl true; rw eq_true; show none ≤ _; simp},
  { convert iff.refl true; simp},
  { convert iff.refl false; simp},
  { simp [H x y]}
end

lemma coe_min (x y : α) [decidable_linear_order α]: ((min x y : α) : with_zero α) = min (x: with_zero α) (y : with_zero α) :=
begin
  by_cases h: x ≤ y,
  { simp [min_eq_left, h] },
  { replace h : y ≤ x := le_of_not_le h,
    simp [min_eq_right, h] }
end

section group
variables [group α]

lemma mul_left_cancel : ∀ {x : with_zero α} (h : x ≠ 0) {y z : with_zero α} ,
  x * y = x * z → y = z
| 0       h := false.elim $ h rfl
| (a : α) h := λ y z h2, begin
  have h3 : (a⁻¹ : with_zero α) * (a * y) = a⁻¹ * (a * z) := by rw h2,
  rwa [←mul_assoc, ←mul_assoc, with_zero.mul_left_inv _ h, one_mul, one_mul] at h3,
end

lemma mul_right_cancel : ∀ {x : with_zero α} (h : x ≠ 0) {y z : with_zero α} ,
  y * x = z * x → y = z
| 0       h := false.elim $ h rfl
| (a : α) h := λ y z h2, begin
  have h3 : (y * a) * a⁻¹ = (z * a) * a⁻¹ := by rw h2,
  rwa [mul_assoc, mul_assoc, with_zero.mul_right_inv _ h, mul_one, mul_one] at h3,
end

end group

end with_zero
