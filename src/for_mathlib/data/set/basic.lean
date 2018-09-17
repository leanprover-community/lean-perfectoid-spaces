import data.set.basic

variables {α : Type*} {β : Type*}

namespace set

lemma prod_quotient_preimage_eq_image [s : setoid α] (g : quotient s → β) {h : α → β} (Hh : h = g ∘ quotient.mk) (r : set (β × β)) :
  {x : quotient s × quotient s | (g x.1, g x.2) ∈ r} =
  (λ a : α × α, (⟦a.1⟧, ⟦a.2⟧)) '' ((λ a : α × α, (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
  set.ext (λ ⟨a₁, a₂⟩, ⟨quotient.induction_on₂ a₁ a₂
    (λ a₁ a₂ h, ⟨(a₁, a₂), h, rfl⟩),
    λ ⟨⟨b₁, b₂⟩, h₁, h₂⟩, show (g a₁, g a₂) ∈ r, from
    have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := prod.ext_iff.1 h₂,
     h₃.1 ▸ h₃.2 ▸ h₁⟩)
end set