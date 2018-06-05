import order.complete_lattice order.order_iso

namespace subrel

variables {α : Type u} [partial_order α] {p : α → Prop}

instance : partial_order {x // p x} :=
{ le := subrel (≤) p,
  le_refl := λ x, le_refl x,
  le_trans := λ x y z, le_trans,
  le_antisymm := λ x y hx hy, subtype.eq $ le_antisymm hx hy }

end subrel
