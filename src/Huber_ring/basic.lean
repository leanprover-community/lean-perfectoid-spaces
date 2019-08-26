import topology.algebra.ring
import ring_theory.algebra_operations
import group_theory.subgroup

import for_mathlib.nonarchimedean.adic_topology
import for_mathlib.open_embeddings
import power_bounded

import for_mathlib.submodule

/-! f-adic rings are called Huber rings by Scholze. A Huber ring is a topological
ring A which contains an open subring A₀ such that the subspace topology on A₀ is
I-adic, where I is a finitely generated ideal of A₀. The pair (A₀, I) is called
a pair of definition (pod) and is not part of the data.

Instead of using a subring A₀, it is slightly more convenient to say
A is an A₀-algebra and the corresponding map A₀ → A is an open topological embedding.
-/

local attribute [instance, priority 0] classical.prop_decidable
noncomputable theory

local notation `𝓘` := with_ideal.ideal
local notation `𝓝` x:70 := nhds x

universes u v

section
open set
local attribute [instance] with_ideal.topological_space

structure Huber_ring.pair_of_definition
  (A₀ : Type*) (A : Type*)
  [comm_ring A₀] [with_ideal A₀]
  [comm_ring A] [topological_space A] [topological_ring A]
  extends algebra A₀ A :=
(emb : topological_space.open_embedding to_fun)
(fin : (𝓘 A₀).fg)

class Huber_ring (A : Type u) extends comm_ring A, topological_space A, topological_ring A :=
(ex_pod : ∃ (A₀ : Type u) [comm_ring A₀] [with_ideal A₀] [Huber_ring.pair_of_definition A₀ A], true)

end

namespace Huber_ring
open topological_add_group
local attribute [instance] with_ideal.topological_space with_ideal.topological_ring
variables {A : Type u} [Huber_ring A]

/-- Picks up a pair of definition for the Huber ring A. -/
def pod (A : Type u) [Huber_ring A] : Type u := classical.some (Huber_ring.ex_pod A)

local notation `spec` := classical.some_spec

def pod_comm_ring : comm_ring (pod A) :=
classical.some (spec (Huber_ring.ex_pod A))

local attribute [instance] pod_comm_ring

def pod_with_ideal : with_ideal (pod A) :=
classical.some (spec $ spec $ Huber_ring.ex_pod A)

local attribute [instance] pod_with_ideal

def pod_pod (A : Type u) [Huber_ring A] : pair_of_definition (pod A) A :=
classical.some (spec $ spec $ spec $ Huber_ring.ex_pod A)

def pod_algebra : algebra (pod A) A :=
(pod_pod A).to_algebra

local attribute [instance] pod_algebra

variables (A)

def pod_fun : pod A → A :=
algebra.to_fun A

instance is_ring_hom_pod_fun : is_ring_hom (pod_fun A) :=
algebra.is_ring_hom

lemma pod_emb : topological_space.open_embedding (pod_fun A) := (pod_pod A).emb

lemma pod_fin : (𝓘 (pod A)).fg := (pod_pod A).fin

lemma exists_pod_subset {U : set A} (hU : U ∈ 𝓝 (0:A)) :
  ∃ n : ℕ, (pod_fun A) '' ((𝓘 $ pod A)^n).carrier ⊆ U :=
begin

  sorry
end

/- lemma exists_pod_subset {U : set A} (hU : U ∈ 𝓝 (0:A)) :
  ∃ (A₀ : Type u) [comm_ring A₀],
    by exactI ∃ [with_ideal A₀],
    by exactI ∃ (rod : ring_of_definition A₀ A),
    by letI := ring_of_definition.to_algebra rod;
    exact (algebra_map A : A₀ → A) '' (𝓘 A₀) ⊆ U :=
begin
  unfreezeI,
  rcases ‹Huber_ring A› with ⟨_, _, _, ⟨A₀, _, _, _, ⟨⟨alg, emb, hf, J, fin, top⟩⟩⟩⟩,
  resetI,
  rw is_ideal_adic_iff at top,
  cases top with H₁ H₂,
  cases H₂ (algebra_map A ⁻¹' U) _ with n hn,
  refine ⟨A₀, ‹_›, ‹_›, ‹_›, ⟨⟨alg, emb, hf, _, _, _⟩, _⟩⟩,
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
end -/
variables {A}

protected lemma nonarchimedean : nonarchimedean A :=
nonarchimedean_of_nonarchimedean_open_embedding (algebra_map A) (pod_emb A) with_ideal.nonarchimedean

instance power_bounded_subring.is_subring : is_subring (power_bounded_subring A) :=
power_bounded_subring.is_subring Huber_ring.nonarchimedean

end Huber_ring
