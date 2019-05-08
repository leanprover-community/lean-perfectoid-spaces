import order.basic
namespace preorder

variables {α : Type*} {β : Type*}

/-- version of preorder.lift which doesn't use type class inference -/
def lift' : preorder β → (α → β) → preorder α := @preorder.lift _ _

end preorder
