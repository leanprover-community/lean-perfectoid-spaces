import topology.subset_properties -- for compactness
import topology.bases
import topology.maps
import for_mathlib.open_embeddings
import tactic.where


#check dense_embedding

namespace topological_space

structure is_spectral (X : Type*) [topological_space X] : Prop :=
(is_compact : compact_space X)
(has_compact_basis : ∃ B : set (set X), is_topological_basis B ∧
  ∀ U ∈ B, compact U ∧ ∀ U V ∈ B, U ∩ V ∈ B)
(irreducible_is_unique_closure : ∀ C : set X, _root_.is_closed C ∧
  is_irreducible C → ∃! (x : X), C = closure {x})

variables (X : Type*) [topological_space X]

-- need to import some definition of Spec before this compiles
-- e.g. Ramon's?
--example (A : Type*) [comm_ring A] : is_spectral (Spec A) := sorry


end topological_space -- namespace
