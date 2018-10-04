import analysis.topology.topological_structures

universe u

variables {R : Type u} [comm_ring R] [topological_space R] [topological_ring R]

/-- Wedhorn Definition 5.27 page 36 -/
definition is_bounded (B : set R) : Prop :=
∀ U ∈ (nhds (0 : R)).sets, ∃ V ∈ (nhds (0 : R)).sets, ∀ v ∈ V, ∀ b ∈ B, v*b ∈ U
