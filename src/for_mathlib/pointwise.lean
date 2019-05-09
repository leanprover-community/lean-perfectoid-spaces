
-- The contents of this file have been PR'd to mathlib #997.
-- !!! WARNING !!!
-- All the instances have been turned into defs; reenable them locally, when needed
-- The lemma mul_le_mul is renamed to mul_subset_mul

import algebra.pointwise
import group_theory.group_action

namespace set
local attribute [instance] set.pointwise_mul_semiring
local attribute [instance] set.singleton.is_monoid_hom
local attribute [instance] pointwise_mul pointwise_add

variables {α : Type*}

instance pointwise_mul_fintype [has_mul α] [decidable_eq α] (s t : set α) [hs : fintype s] [ht : fintype t] :
  fintype (s * t : set α) := by {rw pointwise_mul_eq_image, apply set.fintype_image}

instance pointwise_add_fintype [has_add α] [decidable_eq α] (s t : set α) [hs : fintype s] [ht : fintype t] :
  fintype (s + t : set α) := by {rw pointwise_add_eq_image, apply set.fintype_image}

attribute [to_additive set.pointwise_add_fintype] set.pointwise_mul_fintype

variables [monoid α]

instance : mul_action α (set α) :=
{ smul := λ a s, ({a} : set α) * s,
  one_smul := one_mul,
  mul_smul := λ _ _ _, show {_} * _ = _,
    by { erw is_monoid_hom.map_mul (singleton : α → set α), apply mul_assoc } }

lemma mem_smul_set {a : α} {s : set α} {x : α} :
  x ∈ a • s ↔ ∃ y ∈ s, x = a * y :=
by { erw mem_pointwise_mul, simp }

lemma smul_set_eq_image {a : α} {s : set α} :
  a • s = (λ b, a * b) '' s :=
set.ext $ λ x,
begin
  simp only [mem_smul_set, exists_prop, mem_image],
  apply exists_congr,
  intro y,
  apply and_congr iff.rfl,
  split; exact eq.symm
end

lemma mul_le_mul {s₁ s₂ t₁ t₂ : set α} (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
  s₁ * t₁ ⊆ s₂ * t₂ :=
by { rintros _ ⟨a, ha, b, hb, rfl⟩, exact ⟨a, hs ha, b, ht hb, rfl⟩ }

instance pointwise_mul_fintype_pow [decidable_eq α] (T : set α) [fintype T] (n : ℕ) :
  fintype (T^n : set α) :=
begin
  induction n with n ih,
  { rw pow_zero, exact set.fintype_singleton _ },
  { rw pow_succ, resetI, exact set.pointwise_mul_fintype _ _ }
end

end set
