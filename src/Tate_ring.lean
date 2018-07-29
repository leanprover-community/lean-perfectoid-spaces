import analysis.topology.topological_structures

-- Scholze : "Recall that a topological ring R is Tate if it contains an
-- open and bounded subring R0 ⊂ R and a topologically nilpotent unit pi ∈ R; such elements are
-- called pseudo-uniformizers.""
-- we need definitions of bounded subsete and topologically nilpotent -- and do we have unit? Probably.
class Tate_ring (R : Type*) extends comm_ring R, topological_space R, topological_ring R :=
(unfinished2 : sorry)

-- need an instance from Tate to Huber
