import topology.algebra.ring
import ring_theory.algebra_operations
import group_theory.subgroup

import power_bounded

import for_mathlib.submodule
import for_mathlib.nonarchimedean.adic_topology
import for_mathlib.open_embeddings

-- f-adic rings are called Huber rings by Scholze. A Huber ring is a topological
-- ring A which contains an open subring A0 such that the subspace topology on A0 is
-- I-adic, where I is a finitely generated ideal of A0. The pair (A0, I) is called
-- a pair of definition (pod) and is not part of the data.

local attribute [instance, priority 0] classical.prop_decidable

universes u v

section
open set topological_space

structure Huber_ring.ring_of_definition
  (A₀ : Type*) (A : Type*)
  [comm_ring A₀] [topological_space A₀] [topological_ring A₀]
  [comm_ring A] [topological_space A] [topological_ring A]
  extends algebra A₀ A :=
(emb : open_embedding to_fun)
(J   : ideal A₀)
(fin : J.fg)
(top : is_ideal_adic J)

class Huber_ring (A : Type u) extends comm_ring A, topological_space A, topological_ring A :=
(pod : ∃ (A₀ : Type u) [comm_ring A₀] [topological_space A₀] [topological_ring A₀],
  by exactI nonempty (Huber_ring.ring_of_definition A₀ A))

end

namespace Huber_ring
open topological_add_group
variables {A : Type u} [Huber_ring A]

protected lemma nonarchimedean : nonarchimedean A :=
begin
  rcases Huber_ring.pod A with ⟨A₀, H₁, H₂, H₃, H₄, emb, J, Hfin, Htop⟩,
  resetI,
  apply nonarchimedean_of_nonarchimedean_open_embedding (algebra_map A) emb,
  exact Htop.nonarchimedean
end

instance power_bounded_subring.is_subring : is_subring (power_bounded_subring A) :=
power_bounded_subring.is_subring Huber_ring.nonarchimedean

lemma exists_pod_subset (U : set A) (hU : U ∈ nhds (0:A)) :
  ∃ (A₀ : Type u) [comm_ring A₀] [topological_space A₀],
    by exactI ∃ [topological_ring A₀],
    by exactI ∃ (rod : ring_of_definition A₀ A),
    by letI := ring_of_definition.to_algebra rod;
    exact (algebra_map A : A₀ → A) '' (rod.J) ⊆ U :=
begin
  unfreezeI,
  rcases ‹Huber_ring A› with ⟨_, _, _, ⟨A₀, _, _, _, ⟨⟨alg, emb, J, fin, top⟩⟩⟩⟩,
  resetI,
  rw is_ideal_adic_iff at top,
  cases top with H₁ H₂,
  cases H₂ (algebra_map A ⁻¹' U) _ with n hn,
  refine ⟨A₀, ‹_›, ‹_›, ‹_›, ⟨⟨alg, emb, _, _, _⟩, _⟩⟩,
  { exact J^(n+1) },
  { exact submodule.fg_pow J fin _, },
  { apply is_ideal_adic_pow top, apply nat.succ_pos },
  { change algebra_map A '' ↑(J ^ (n + 1)) ⊆ U,
    rw set.image_subset_iff,
    exact set.subset.trans (J.pow_le_pow $ nat.le_succ n) hn },
  { apply emb.continuous.tendsto,
    rw show algebra.to_fun A (0:A₀) = 0,
    { apply is_ring_hom.map_zero },
    exact hU }
end

end Huber_ring
