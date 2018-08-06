import analysis.topology.topological_structures
import for_mathlib.subring

-- Scholze : "Recall that a topological ring R is Tate if it contains an
-- open and bounded subring R₀ ⊂ R and a topologically nilpotent unit ϖ ∈ R; such elements are
-- called pseudo-uniformizers."

variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]

def topologically_nilpotent (r : R) : Prop :=
∀ U ∈ (nhds (0 :R)).sets, ∃ N : ℕ, ∀ n : ℕ, n > N → r^n ∈ U

definition is_pseudo_uniformizer (ϖ : units R) : Prop := topologically_nilpotent ϖ.val

class Tate_ring (R : Type*) extends comm_ring R, topological_space R, topological_ring R :=
(R₀ : set R)
(R₀_is_open : is_open R₀)
(R₀_is_subring : is_subring R₀)
(ϖ : units R)
(ϖ_is_pseudo_uniformizer : is_pseudo_uniformizer ϖ)

-- need an instance from Tate to Huber
