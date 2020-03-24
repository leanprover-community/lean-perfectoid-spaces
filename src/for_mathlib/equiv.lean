import data.equiv.basic algebra.group
import order.basic logic.basic -- needed for order stuff
import for_mathlib.with_zero
import data.equiv.mul_add

def equiv.with_zero_equiv {α β : Type*} (h : α ≃ β) : (with_zero α) ≃ (with_zero β) :=
{ to_fun := with_zero.map h,
  inv_fun := with_zero.map h.symm,
  left_inv := λ x, begin cases x, refl, show some _ = some _, congr, exact h.left_inv x end,
  right_inv := λ x, begin cases x, refl, show some _ = some _, congr, exact h.right_inv x end,
}

variables {α : Type*} {β : Type*} {γ : Type*}

namespace mul_equiv
variables [monoid α] [monoid β] [monoid γ]

def to_with_zero_mul_equiv (h : α ≃* β) : (with_zero α) ≃* (with_zero β) :=
{ map_mul' := λ x y,
  begin cases x; cases y; try { refl},
    show some _ = some _, congr, exact @is_mul_hom.map_mul _ _ _ _ h _ x y
  end,
  ..h.to_equiv.with_zero_equiv }

end mul_equiv

-- from here on -- should this go in data.equiv.order?

structure le_equiv (α β : Type*) [has_le α] [has_le β] extends α ≃ β :=
(le_map : ∀ ⦃x y⦄, x ≤ y ↔ to_fun x ≤ to_fun y)

infix ` ≃≤ `:50 := le_equiv

namespace le_equiv

variables (X : Type*) [has_le X] (Y : Type*) [has_le Y] (Z : Type*) [has_le Z]

variables {X} {Y} {Z}

@[refl] def refl (X : Type*) [has_le X] : X ≃≤ X :=
{ le_map := λ _ _, iff.rfl,
  ..equiv.refl _}

@[symm] def symm (h : X ≃≤ Y) : Y ≃≤ X :=
{ le_map := λ x₁ x₂, begin
    convert (@le_equiv.le_map _ _ _ _ h (h.to_equiv.symm x₁) (h.to_equiv.symm x₂)).symm,
    exact (h.right_inv x₁).symm, exact (h.right_inv x₂).symm end,
  ..h.to_equiv.symm
}

@[trans] def trans (h1 : X ≃≤ Y) (h2 : Y ≃≤ Z) : X ≃≤ Z :=
{ le_map := λ x₁ x₂, iff.trans (@le_equiv.le_map _ _ _ _ h1 x₁ x₂)
    (@le_equiv.le_map _ _ _ _ h2 (h1.to_fun x₁) (h1.to_fun x₂)),
  ..equiv.trans h1.to_equiv h2.to_equiv
}

end le_equiv

def preorder_equiv (α β : Type*) [preorder α] [preorder β] := le_equiv α β

structure lt_equiv (α β : Type*) [has_lt α] [has_lt β] extends α ≃ β :=
(lt_map : ∀ ⦃x y⦄, x < y ↔ to_fun x < to_fun y)

infix ` ≃< `:50 := lt_equiv

-- iff for ordering -- is this in mathlib?
def linear_order_le_iff_of_monotone_injective {α : Type*} {β : Type*}
  [linear_order α] [linear_order β] {f : α → β}
  (hf : function.injective f)
  (h2 : ∀ x y, x ≤ y → f x ≤ f y)
  : ∀ x y, x ≤ y ↔ f x ≤ f y :=
λ x y, ⟨h2 x y, λ h3, le_of_not_lt $ λ h4, not_lt_of_le h3 $ lt_of_le_of_ne
 (h2 y x $ le_of_lt h4) $ λ h5, ne_of_lt h4 $ hf h5⟩

namespace preorder_equiv

variables [preorder α] [preorder β] [preorder γ]

@[refl] def refl (α : Type*) [preorder α] : α ≃≤ α :=
{ le_map := λ _ _, iff.rfl,
..equiv.refl _}

@[symm] def symm (h : α ≃≤ β) : β ≃≤ α :=
{ le_map := λ x y, begin
    convert (@le_equiv.le_map _ _ _ _ h (h.to_equiv.symm x) (h.to_equiv.symm y)).symm,
    { exact (h.right_inv x).symm},
    { exact (h.right_inv y).symm},
  end
  ..h.to_equiv.symm}

@[trans] def trans (h1 : α ≃≤ β) (h2 : β ≃≤ γ) : (α ≃≤ γ) :=
{ le_map := λ x y,
    iff.trans (@le_equiv.le_map _ _ _ _ h1 x y)
      (@le_equiv.le_map _ _ _ _ h2 (h1.to_equiv x) (h1.to_equiv y)),
  ..equiv.trans h1.to_equiv h2.to_equiv }

end preorder_equiv

def equiv.lt_map_of_le_map {α : Type*} {β : Type*} [preorder α] [preorder β]
  (he : α ≃ β) (hle : ∀ x y, x ≤ y ↔ he x ≤ he y) : (∀ x y, x < y ↔ he x < he y) :=
λ x y, by rw [lt_iff_le_not_le, hle x y, hle y x, lt_iff_le_not_le]

def equiv.le_map_iff_lt_map {α : Type*} {β : Type*} [partial_order α] [partial_order β]
  (he : α ≃ β) : (∀ x y, x ≤ y ↔ he x ≤ he y) ↔ (∀ x y, x < y ↔ he x < he y) :=
⟨equiv.lt_map_of_le_map he, λ hlt x y, by rw [le_iff_eq_or_lt, le_iff_eq_or_lt];
  exact or_congr (by simp) (hlt x y)⟩

def preorder_equiv.to_lt_equiv {α : Type*} {β : Type*} [preorder α] [preorder β]
  (he : α ≃≤ β) : α ≃< β := {lt_map := he.to_equiv.lt_map_of_le_map he.le_map
  ..he.to_equiv}

def preorder_equiv.to_with_zero_preorder_equiv {α : Type*} {β : Type*} [preorder α] [preorder β]
  (he : α ≃≤ β) : (with_zero α) ≃≤ (with_zero β) :=
  { le_map := with_zero.map_le he.le_map
    ..he.to_equiv.with_zero_equiv}

-- equiv of top spaces is already done -- it's called homeomorph in topology/constructions.lean
