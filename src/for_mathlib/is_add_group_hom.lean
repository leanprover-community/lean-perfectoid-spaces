import algebra.group

variables {α : Type*} {β : Type*} [add_group α] [add_group β]
class is_add_group_hom  (f : α → β) : Prop :=
(add : ∀ a b : α, f (a + b) = f a + f b)

namespace is_add_group_hom

variables (f : α → β) [is_add_group_hom f]

theorem zero : f 0 = 0 :=
add_self_iff_eq_zero.1 $ by simp [(add f 0 0).symm]


lemma neg (a : α) : f (-a) = -(f a) :=
eq.symm $ neg_eq_of_add_eq_zero $ by simp [(add f a (-a)).symm, zero f]

lemma sub (a b : α) : f (a - b) = f a - f b :=
calc f (a - b) = f (a + -b)   : rfl
           ... = f a + f (-b) : add f _ _
           ... = f a - f b    : by  simp[neg f]

instance comp {γ} [add_group γ] (g : β → γ) [is_add_group_hom g] :
  is_add_group_hom (g ∘ f) :=
⟨λ x y, calc
  g (f (x + y)) = g (f x + f y)       : by rw add f
  ...           = g (f x) + g (f y)   : by rw add g⟩
end is_add_group_hom
