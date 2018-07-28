import analysis.topology.topological_space
import analysis.topology.uniform_space

@[class] def opens (X : Type*) [topological_space X] := {U : set X // is_open U}

namespace opens

variables (X : Type*) [topological_space X]

instance : has_coe (opens X) (set X) := ⟨λU, U.1⟩

instance : has_mem X (opens X) := ⟨λx U, x ∈ U.1⟩

instance : has_inter (opens X) := ⟨λ U V, ⟨U.1 ∩ V.1, is_open_inter U.2 V.2⟩⟩

instance : has_union (opens X) := ⟨λ U V, ⟨U.1 ∪ V.1, is_open_union U.2 V.2⟩⟩

instance : has_emptyc (opens X) := ⟨⟨∅, is_open_empty⟩⟩
end opens

-- peredicates we need for topological rings

-- We need to think whether we could directly use the class t2_space (which is not using opens though)
definition is_hausdorff (α : Type*) [topological_space α] : Prop := 
  ∀ x y, x ≠ y → ∃ u v : opens α, x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅

-- Wedhorn Definition 5.31 page 38
definition is_complete (α : Type*) [uniform_space α] := 
  is_hausdorff α ∧ ∀ {f : filter α}, cauchy f → ∃ x, f ≤ nhds x