import data.finsupp

universes u v w

#check @finsupp.prod_neg_index

namespace finsupp

variables {α : Type u} {β : Type v} {γ : Type w}
variables [decidable_eq α] [decidable_eq β] [add_group β] [comm_group γ]
variables {g : α →₀ β} {h h₁ h₂ : α → β → γ}

theorem prod_mul_distrib : finsupp.prod g (λ a b, h₁ a b * h₂ a b) =
  finsupp.prod g h₁ * finsupp.prod g h₂ :=
finset.prod_mul_distrib

theorem prod_const_one : finsupp.prod g (λ a b, (1 : γ)) = 1 :=
finset.prod_const_one

theorem prod_inv : finsupp.prod g (λ a b, (h a b)⁻¹) = (finsupp.prod g h)⁻¹ :=
eq_inv_of_mul_eq_one $ by rw [← prod_mul_distrib]; simp only [inv_mul_self]; exact prod_const_one

theorem prod_neg_index' (h0 : ∀ a, h a 0 = 1) (hn : ∀ a b, h a (-b) = (h a b)⁻¹) :
  finsupp.prod (-g) h = (finsupp.prod g h)⁻¹ :=
by rw [prod_neg_index h0]; simp only [hn]; exact prod_inv

end finsupp
