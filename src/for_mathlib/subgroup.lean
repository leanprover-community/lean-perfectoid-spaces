import group_theory.subgroup
import algebra.pi_instances

namespace add_group -- This is PR'd to mathlib in #1069
-- TODO(jmc): generalise using to_additive
variables {α : Type*} {β : Type*} [add_group α] [add_group β] (f : α → β) [is_add_group_hom f]

lemma image_closure (s : set α) : f '' closure s = closure (f '' s) :=
le_antisymm
  (by rintros _ ⟨x, hx, rfl⟩; exact in_closure.rec_on hx
  (λ a ha, mem_closure ⟨a, ha, rfl⟩)
  (by {rw [is_add_monoid_hom.map_zero f]; apply is_add_submonoid.zero_mem, })
  (by {intros, rw [is_add_group_hom.map_neg f]; apply is_add_subgroup.neg_mem, assumption })
  (by {intros, rw [is_add_monoid_hom.map_add f]; apply is_add_submonoid.add_mem, assumption' }))
  (closure_subset $ set.image_subset _ subset_closure)

end add_group
