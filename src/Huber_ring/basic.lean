import topology.algebra.ring
import ring_theory.algebra_operations
import group_theory.subgroup

import power_bounded

-- f-adic rings are called Huber rings by Scholze. A Huber ring is a topological
-- ring A which contains an open subring A0 such that the subspace topology on A0 is
-- I-adic, where I is a finitely generated ideal of A0. The pair (A0, I) is called
-- a pair of definition (pod) and is not part of the data.

local attribute [instance, priority 0] classical.prop_decidable

universes u v

section
open set

structure Huber_ring.ring_of_definition
  (A₀ : Type*) [comm_ring A₀] [topological_space A₀] [topological_ring A₀]
  (A : Type*) [comm_ring A] [topological_space A] [topological_ring A]
  extends algebra A₀ A :=
(emb : embedding to_fun)
(hf  : is_open (range to_fun))
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
  rcases Huber_ring.pod A with ⟨A₀, H₁, H₂, H₃, H₄, emb, hf, J, Hfin, Htop⟩,
  resetI,
  apply nonarchimedean_of_nonarchimedean_open_embedding (algebra_map A) emb hf,
  exact Htop.nonarchimedean,
end

instance power_bounded_subring.is_subring : is_subring (power_bounded_subring A) :=
power_bounded_subring.is_subring Huber_ring.nonarchimedean

end Huber_ring
