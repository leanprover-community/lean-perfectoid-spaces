import order.basic
namespace preorder

variables {α : Type*} {β : Type*}

--def comap [preorder β] (f : α → β) : preorder α :=
--{ le := λ x y, f x ≤ f y,
--  le_refl := λ x, le_refl (f x),
--  le_trans := λ x y z, le_trans (f x) (f y) (f z)}

/-- version of preorder.lift which doesn't use type class inference -/
def lift' : preorder β → (α → β) → preorder α := @preorder.lift _ _

end preorder
