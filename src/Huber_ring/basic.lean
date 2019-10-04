import topology.algebra.ring
import ring_theory.algebra_operations
import group_theory.subgroup

import power_bounded

import for_mathlib.submodule
import for_mathlib.nonarchimedean.adic_topology
import for_mathlib.open_embeddings

/-!
# Huber rings

Huber rings (called “f-adic rings” by Huber and [Wedhorn], but Scholze renamed them)
play a crucial role in the theory of adic spaces,
as one of the main ingredients in the definition of so-called “Huber pairs”.
They are topological rings that satisfy a certain topological finiteness condition.

## Implementation details

In the following definition we record the ideal J as data,
whereas usually one takes its existence as a property.
For practical purposes it is however easier to package it as data.
In the definition of Huber ring (below it), we return to the existence statement
so that `Huber_ring` is a property of a topological commutative ring not involving any data.
-/

local attribute [instance, priority 0] classical.prop_decidable

universes u v

section
open set topological_space

/-- A “ring of definition” of a topological ring A is an open subring A₀
that has a finitely generated ideal J such that the topology on A₀ is J-adic.
See [Wedhorn, Def 6.1] -/
structure Huber_ring.ring_of_definition
  (A₀ : Type*) (A : Type*)
  [comm_ring A₀] [topological_space A₀] [topological_ring A₀]
  [comm_ring A] [topological_space A] [topological_ring A]
  extends algebra A₀ A :=
(emb : open_embedding to_fun)
(J   : ideal A₀)
(fin : J.fg)
(top : is_ideal_adic J)

/-- A Huber ring is a topological ring A that contains an open subring A₀
such that the subspace topology on A₀ is I-adic,
where I is a finitely generated ideal of A₀.
The pair (A₀, I) is called a pair of definition (pod) and is not part of the data.
(The name “Huber ring” was introduced by Scholze.
Before that, they were called f-adic rings.) See [Wedhorn, Def 6.1] -/
class Huber_ring (A : Type u) extends comm_ring A, topological_space A, topological_ring A :=
(pod : ∃ (A₀ : Type u) [comm_ring A₀] [topological_space A₀] [topological_ring A₀],
  by exactI nonempty (Huber_ring.ring_of_definition A₀ A))

end

namespace Huber_ring
open topological_add_group
variables {A : Type u} [Huber_ring A]

/-- A Huber ring is nonarchimedean. -/
protected lemma nonarchimedean : nonarchimedean A :=
begin
  rcases Huber_ring.pod A with ⟨A₀, H₁, H₂, H₃, H₄, emb, J, Hfin, Htop⟩,
  resetI,
  apply nonarchimedean_of_nonarchimedean_open_embedding (algebra_map A) emb,
  exact Htop.nonarchimedean
end

instance power_bounded_subring.is_subring : is_subring (power_bounded_subring A) :=
power_bounded_subring.is_subring Huber_ring.nonarchimedean

/-- For every neighbourhood U of 0 ∈ A,
there exists a pair of definition (A₀, J) such that J ⊆ U. -/
lemma exists_pod_subset (U : set A) (hU : U ∈ nhds (0:A)) :
  ∃ (A₀ : Type u) [comm_ring A₀] [topological_space A₀],
    by exactI ∃ [topological_ring A₀],
    by exactI ∃ (rod : ring_of_definition A₀ A),
    by letI := ring_of_definition.to_algebra rod;
    exact (algebra_map A : A₀ → A) '' (rod.J) ⊆ U :=
begin
  -- We start by unpacking the fact that A is a Huber ring.
  unfreezeI,
  rcases ‹Huber_ring A› with ⟨_, _, _, ⟨A₀, _, _, _, ⟨⟨alg, emb, J, fin, top⟩⟩⟩⟩,
  resetI,
  rw is_ideal_adic_iff at top,
  cases top with H₁ H₂,
  -- There exists an n such that J^n ⊆ U. Choose such an n.
  cases H₂ (algebra_map A ⁻¹' U) _ with n hn,
  -- Now it is time to pack everything up again.
  refine ⟨A₀, ‹_›, ‹_›, ‹_›, ⟨⟨alg, emb, _, _, _⟩, _⟩⟩,
  { -- We have to use the ideal J^(n+1), because A₀ is not J^0-adic.
    exact J^(n+1) },
  { exact submodule.fg_pow J fin _, },
  { apply is_ideal_adic_pow top, apply nat.succ_pos },
  { show algebra_map A '' ↑(J ^ (n + 1)) ⊆ U,
    rw set.image_subset_iff,
    exact set.subset.trans (ideal.pow_le_pow $ nat.le_succ n) hn },
  { apply emb.continuous.tendsto,
    rw show algebra.to_fun A (0:A₀) = 0,
    { apply is_ring_hom.map_zero },
    exact hU }
end

end Huber_ring


#sanity_check
#doc_blame


