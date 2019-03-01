import topology.basic
import topology.uniform_space.basic

open topological_space

-- predicates we need for topological rings

-- We need to think whether we could directly use the class t2_space (which is not using opens though)
definition is_hausdorff (α : Type*) [topological_space α] : Prop :=
  ∀ x y, x ≠ y → ∃ u v : opens α, x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅

-- Wedhorn Definition 5.31 page 38
definition is_complete_hausdorff (α : Type*) [uniform_space α] :=
  is_hausdorff α ∧ ∀ {f : filter α}, cauchy f → ∃ x, f ≤ nhds x
