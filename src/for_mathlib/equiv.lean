import data.equiv.basic

def subtype_equiv_of_subtype' {α β : Type*} {p : α → Prop} {q : β → Prop}
  (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) : {a : α // p a} ≃ {b : β // q b} :=
⟨λ x, ⟨e x.1, (h _).1 x.2⟩,
 λ y, ⟨e.symm y.1, (h _).2 (by simp; exact y.2)⟩,
 λ ⟨x, h⟩, subtype.eq' $ by simp,
 λ ⟨y, h⟩, subtype.eq' $ by simp⟩