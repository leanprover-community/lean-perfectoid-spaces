import data.equiv.basic algebra.group
import order.basic logic.basic -- needed for order stuff

-- A lot of this is in PR 789

variables {α : Type*} {β : Type*} {γ : Type*}

@[to_additive is_add_hom]
def is_mul_hom {α β : Type*} [has_mul α] [has_mul β] (f : α → β) : Prop :=
∀ x y, f (x * y) = f x * f y

namespace is_mul_hom
variables [has_mul α] [has_mul β] [has_mul γ]

@[to_additive is_add_hom.id]
lemma id : is_mul_hom (id : α → α) := λ _ _, rfl

@[to_additive is_add_hom.comp]
lemma comp {f : α → β} {g : β → γ} (hf : is_mul_hom f) (hg : is_mul_hom g) : is_mul_hom (g ∘ f) :=
λ x y, by show _ = g _ * g _; rw [←hg, ←hf]

end is_mul_hom

structure add_equiv (α β : Type*) [has_add α] [has_add β] extends α ≃ β :=
(add_hom : is_add_hom to_fun)

infix ` ≃+ `:50 := add_equiv

namespace add_equiv

variables [has_add α] [has_add β] [has_add γ]

@[refl] def refl (α : Type*) [has_add α] : α ≃+ α :=
{ add_hom := λ _ _,rfl,
  ..equiv.refl _}

@[symm] def symm (h : α ≃+ β) : β ≃+ α :=
{ add_hom := λ n₁ n₂, function.injective_of_left_inverse h.left_inv begin
   rw h.add_hom, unfold equiv.symm, rw [h.right_inv, h.right_inv, h.right_inv], end
  ..h.to_equiv.symm}

@[trans] def trans (h1 : α ≃+ β) (h2 : β ≃+ γ) : (α ≃+ γ) :=
{ add_hom := is_add_hom.comp h1.add_hom h2.add_hom,
  ..equiv.trans h1.to_equiv h2.to_equiv }

end add_equiv

structure mul_equiv (α β : Type*) [has_mul α] [has_mul β] extends α ≃ β :=
(mul_hom : is_mul_hom to_fun)

infix ` ≃* `:50 := mul_equiv

namespace mul_equiv

variables [has_mul α] [has_mul β] [has_mul γ]

@[refl] def refl (α : Type*) [has_mul α] : α ≃* α :=
{ mul_hom := λ _ _,rfl,
..equiv.refl _}

@[symm] def symm (h : α ≃* β) : β ≃* α :=
{ mul_hom := λ n₁ n₂, function.injective_of_left_inverse h.left_inv begin
   rw h.mul_hom, unfold equiv.symm, rw [h.right_inv, h.right_inv, h.right_inv], end
  ..h.to_equiv.symm}

@[trans] def trans (h1 : α ≃* β) (h2 : β ≃* γ) : (α ≃* γ) :=
{ mul_hom := is_mul_hom.comp h1.mul_hom h2.mul_hom,
  ..equiv.trans h1.to_equiv h2.to_equiv }

end mul_equiv

namespace mul_equiv

variables [monoid α] [monoid β] [monoid γ]

lemma one (h : equiv α β) (hom : ∀ x y, h (x * y) = h x * h y) :
  h 1 = 1 :=
by rw [←mul_one (h 1), ←h.apply_symm_apply 1, ←hom]; simp

instance is_monoid_hom (h : α ≃* β) : is_monoid_hom h.to_equiv := {
  map_one := mul_equiv.one h.to_equiv h.mul_hom,
  map_mul := h.mul_hom }

end mul_equiv

-- equiv of monoids

def monoid_equiv (α : Type*) (β : Type*) [monoid α] [monoid β] := mul_equiv α β

namespace monoid_equiv
variables [monoid α] [monoid β] [monoid γ]

@[refl] def refl (α : Type*) [monoid α] : monoid_equiv α α := mul_equiv.refl α

@[symm] def symm : monoid_equiv α β → monoid_equiv β α := mul_equiv.symm

@[trans] def trans : monoid_equiv α β → monoid_equiv β γ → monoid_equiv α γ := mul_equiv.trans

end monoid_equiv

-- equiv of groups

def group_equiv (α : Type*) (β : Type*) [group α] [group β] := mul_equiv α β

namespace group_equiv
variables [group α] [group β] [group γ]

@[refl] def refl (α : Type*) [group α] : group_equiv α α := mul_equiv.refl α

@[symm] def symm : group_equiv α β → group_equiv β α := mul_equiv.symm

@[trans] def trans : group_equiv α β → group_equiv β γ → group_equiv α γ := mul_equiv.trans

--definition with_zero.map_comp := is_lawful_functor.map_comp

def to_with_zero_monoid_equiv (h : group_equiv α β) : monoid_equiv (with_zero α) (with_zero β) :=
{ to_fun := option.map (h.to_equiv),
  inv_fun := option.map (h.to_equiv.symm),
  left_inv := begin  sorry, end,
  right_inv := sorry,
  mul_hom := sorry }

end group_equiv

-- equiv of add_groups needs doing

namespace mul_equiv

variables [group α] [group β] [group γ]

instance is_group_hom (h : α ≃* β) : is_group_hom h.to_equiv := ⟨h.mul_hom⟩

end mul_equiv

-- equiv of add_groups
namespace add_equiv

variables [add_group α] [add_group β] [add_group γ]

instance is_add_group_hom (h : α ≃+ β) : is_add_group_hom h.to_equiv := ⟨h.add_hom⟩

end add_equiv


namespace units

variables [monoid α] [monoid β] [monoid γ]
(f : α → β) (g : β → γ) [is_monoid_hom f] [is_monoid_hom g]

def map_equiv (h : α ≃* β) : units α ≃* units β :=
{ to_fun := map h.to_equiv,
  inv_fun := map h.symm.to_equiv,
  left_inv := λ u, ext $ h.left_inv u,
  right_inv := λ u, ext $ h.right_inv u,
  mul_hom := λ a b, units.ext $ h.mul_hom a b}

end units

-- from here on -- should this go in data.equiv.order?

structure preorder_equiv (α β : Type*) [preorder α] [preorder β] extends α ≃ β :=
(le_map : ∀ {x y}, x ≤ y ↔ to_fun x ≤ to_fun y)

infix ` ≃≤ `:50 := preorder_equiv

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
    convert (@le_map _ _ _ _ h (h.to_equiv.symm x) (h.to_equiv.symm y)).symm,
    { exact (h.right_inv x).symm},
    { exact (h.right_inv y).symm},
  end
  ..h.to_equiv.symm}

@[trans] def trans (h1 : α ≃≤ β) (h2 : β ≃≤ γ) : (α ≃≤ γ) :=
{ le_map := λ x y,
    iff.trans (@le_map _ _ _ _ h1 x y) (@le_map _ _ _ _ h2 (h1.to_equiv x) (h1.to_equiv y)),
  ..equiv.trans h1.to_equiv h2.to_equiv }

end preorder_equiv

def equiv.lt_map_of_le_map {α : Type*} {β : Type*} [preorder α] [preorder β]
  (he : α ≃ β) (hle : ∀ x y, x ≤ y ↔ he x ≤ he y) : (∀ x y, x < y ↔ he x < he y) :=
λ x y, by rw [lt_iff_le_not_le, hle x y, hle y x, lt_iff_le_not_le]

def equiv.le_map_iff_lt_map {α : Type*} {β : Type*} [partial_order α] [partial_order β]
  (he : α ≃ β) : (∀ x y, x ≤ y ↔ he x ≤ he y) ↔ (∀ x y, x < y ↔ he x < he y) :=
⟨equiv.lt_map_of_le_map he, λ hlt x y, by rw [le_iff_eq_or_lt, le_iff_eq_or_lt];
  exact or_congr (by simp) (hlt x y)⟩
