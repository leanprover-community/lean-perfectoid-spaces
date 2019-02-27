import order.basic
open function

variables {α : Type*} {β : Type*}

def strict_mono [preorder α] [preorder β] (f : α → β) :=
∀ a b, a < b → f a < f b

namespace strict_mono

variables [linear_order α] [preorder β] {f : α → β}

lemma lt_iff_lt (H : strict_mono f) {a b} :
  f a < f b ↔ a < b :=
⟨λ h, ((lt_trichotomy b a)
  .resolve_left $ λ h', lt_asymm h $ H _ _ h')
  .resolve_left $ λ e, ne_of_gt h $ congr_arg _ e, H _ _⟩

lemma le_iff_le (H : strict_mono f) {a b} :
  f a ≤ f b ↔ a ≤ b :=
⟨λ h, le_of_not_gt $ λ h', not_le_of_lt (H b a h') h,
 λ h, (lt_or_eq_of_le h).elim (λ h', le_of_lt (H _ _ h')) (λ h', h' ▸ le_refl _)⟩

lemma injective (H : strict_mono f) : function.injective f
| a b e := ((lt_trichotomy a b)
  .resolve_left $ λ h, ne_of_lt (H _ _ h) e)
  .resolve_right $ λ h, ne_of_gt (H _ _ h) e

lemma monotone (H : strict_mono f) :
  monotone f :=
λ a b, iff.mpr $ H.le_iff_le

end strict_mono

section
variables [partial_order α] [partial_order β] {f : α → β}

lemma strict_mono_of_monotone_of_injective (h₁ : monotone f) (h₂ : injective f) :
  strict_mono f :=
λ a b h,
begin
  rw lt_iff_le_and_ne at ⊢ h,
  exact ⟨h₁ h.1, λ e, h.2 (h₂ e)⟩
end

end
