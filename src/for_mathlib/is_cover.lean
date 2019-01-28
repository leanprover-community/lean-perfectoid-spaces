import topology.basic

definition is_cover {X γ : Type} (U : γ → set X) := ∀ x, ∃ i, x ∈ U i

structure is_open_cover {X γ : Type} [H : topological_space X] (U : γ → set X) := 
(is_open : ∀ i, H.is_open (U i))
(is_cover : is_cover U) 

