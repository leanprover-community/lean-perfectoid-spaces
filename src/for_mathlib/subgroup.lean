import group_theory.subgroup

-- this should go around https://github.com/leanprover-community/mathlib/blob/8fbf296d9a50aaf7ea56832ac208a4ed6bbcae8e/src/group_theory/subgroup.lean#L443

variables {α : Type*} {β : Type*} [group α] [group β]

namespace is_group_hom

@[to_additive is_add_group_hom.zero_ker_neg']
lemma one_ker_inv' (f : α → β) [is_group_hom f] {a b : α} (h : f (a⁻¹ * b) = 1) : f a = f b :=
begin
  rw [mul f, inv f] at h,
  apply eq_of_inv_eq_inv,
  rw eq_inv_of_mul_eq_one h
end

@[to_additive is_add_group_hom.neg_ker_zero']
lemma inv_ker_one' (f : α → β) [is_group_hom f] {a b : α} (h : f a = f b) : f (a⁻¹ * b) = 1 :=
have (f a)⁻¹ * f b = 1, by rw [h, mul_left_inv],
by rwa [←inv f, ←mul f] at this

@[to_additive is_add_group_hom.zero_iff_ker_neg]
lemma one_iff_ker_inv' (f : α → β) [is_group_hom f] (a b : α) : f a = f b ↔ f (a⁻¹ * b) = 1 :=
⟨inv_ker_one' f, one_ker_inv' f⟩

@[to_additive is_add_group_hom.neg_iff_ker]
lemma inv_iff_ker' (f : α → β) [w : is_group_hom f] (a b : α) : f a = f b ↔ a⁻¹ * b ∈ ker f :=
by rw [mem_ker]; exact one_iff_ker_inv' _ _ _

end is_group_hom
