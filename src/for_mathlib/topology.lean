import topology.opens
import topology.uniform_space.cauchy
import topology.algebra.group

section
open topological_space

-- predicates we need for topological rings

-- We need to think whether we could directly use the class t2_space (which is not using opens though)
definition is_hausdorff (α : Type*) [topological_space α] : Prop :=
  ∀ x y, x ≠ y → ∃ u v : opens α, x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅

-- Wedhorn Definition 5.31 page 38
definition is_complete_hausdorff (α : Type*) [uniform_space α] :=
  is_hausdorff α ∧ ∀ {f : filter α}, cauchy f → ∃ x, f ≤ nhds x
end

@[to_additive topological_add_group.ext, extensionality]
lemma topological_group.ext {G : Type*} [group G] (t t' : topological_space G)
  (tg : @topological_group G t _) (tg' : @topological_group G t' _)
  (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
eq_of_nhds_eq_nhds $ λ x, by
  rw [← @nhds_translation_mul_inv G t _ _ x , ← @nhds_translation_mul_inv G t' _ _ x , ← h]
