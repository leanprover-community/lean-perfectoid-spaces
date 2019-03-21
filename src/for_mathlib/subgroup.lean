import group_theory.subgroup
import algebra.pi_instances

import for_mathlib.submonoid

section
variables {α : Type*} [group α] {β : Type*} [group β]

@[to_additive is_add_subgroup.inter]
instance is_subgroup.inter (s₁ s₂ : set α) [is_subgroup s₁] [is_subgroup s₂] :
  is_subgroup (s₁ ∩ s₂) :=
{ inv_mem := λ x hx, ⟨is_subgroup.inv_mem hx.1, is_subgroup.inv_mem hx.2⟩,
  ..is_submonoid.inter s₁ s₂ }

@[to_additive is_add_subgroup.prod]
instance is_subgroup.prod (s : set α) (t :  set β) [is_subgroup s] [is_subgroup t] :
  is_subgroup (s.prod t) :=
{ one_mem := by rw set.mem_prod; split; apply is_submonoid.one_mem,
  mul_mem := by intros; rw set.mem_prod at *; split; apply is_submonoid.mul_mem; tauto,
  inv_mem := by intros; rw set.mem_prod at *; split; apply is_subgroup.inv_mem; tauto }

end


-- this should go around https://github.com/leanprover-community/mathlib/blob/8fbf296d9a50aaf7ea56832ac208a4ed6bbcae8e/src/group_theory/subgroup.lean#L443

-- This is all in PR #790

namespace is_group_hom
variables {α : Type*} {β : Type*} [group α] [group β]

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

section
variables {α : Type*} [comm_monoid α] {β : Type*}

-- @[to_additive sum_mem_closure]
-- lemma prod_mem_closure (s : set α) (ι : finset β) (f : β → α) (h : ∀ i ∈ ι, f i ∈ s) :
--   ι.prod f ∈ monoid.closure s := sorry

end

namespace add_monoid
variables {α : Type*} [add_comm_monoid α] {β : Type*}

local attribute [instance] classical.prop_decidable

lemma sum_mem_closure (s : set α) (ι : finset β) (f : β → α) (h : ∀ i ∈ ι, f i ∈ s) :
  ι.sum f ∈ add_monoid.closure s :=
begin
  revert h,
  apply finset.induction_on ι,
  { intros, rw finset.sum_empty, apply is_add_submonoid.zero_mem },
  { intros i ι' hi IH h,
    rw finset.sum_insert hi,
    apply is_add_submonoid.add_mem,
    { apply add_monoid.subset_closure,
      apply h,
      apply finset.mem_insert_self },
    { apply IH,
      intros i' hi',
      apply h,
      apply finset.mem_insert_of_mem hi' } }
end

end add_monoid
