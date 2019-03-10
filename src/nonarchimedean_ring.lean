import topology.algebra.ring
import topology.opens

/- A commutative topological ring is _non-archimedean_ if every open subset
   containing 0 also contains an open additive subgroup.

-/
open topological_space

definition nonarchimedean (G : Type*)
  [add_group G] [topological_space G] [topological_add_group G] : Prop :=
∀ U ∈ nhds (0 : G), ∃ V : set G, is_add_subgroup V ∧ _root_.is_open V ∧ V ⊆ U
