import data.set.basic
import data.quot
import order.order_iso

variables {α : Type*} {β : Type*} [s : setoid α]

namespace setoid

def comap (t : setoid β) (f : α → β) : setoid α :=
{ r := _, iseqv := preimage_equivalence f t.iseqv }

end setoid

namespace quotient
lemma prod_preimage_eq_image (g : quotient s → β) {h : α → β} (Hh : h = g ∘ quotient.mk) (r : set (β × β)) :
  {x : quotient s × quotient s | (g x.1, g x.2) ∈ r} =
  (λ a : α × α, (⟦a.1⟧, ⟦a.2⟧)) '' ((λ a : α × α, (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
  set.ext (λ ⟨a₁, a₂⟩, ⟨quotient.induction_on₂ a₁ a₂
    (λ a₁ a₂ h, ⟨(a₁, a₂), h, rfl⟩),
    λ ⟨⟨b₁, b₂⟩, h₁, h₂⟩, show (g a₁, g a₂) ∈ r, from
    have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := prod.ext_iff.1 h₂,
     h₃.1 ▸ h₃.2 ▸ h₁⟩)

end quotient

lemma quot_mk_quotient_mk {α :Type*} [setoid α] (a : α) : quot.mk setoid.r a = ⟦a⟧ :=
rfl

noncomputable
def habitant_of_quotient_habitant {α : Type*} {s : setoid α} (x : quotient s) : α :=
(classical.inhabited_of_nonempty $ (nonempty_quotient_iff s).1 ⟨x⟩).default
