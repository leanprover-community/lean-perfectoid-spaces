import for_mathlib.integral_closure

import power_bounded Huber_ring.basic

/-!
# Huber pairs

This short file defines Huber pairs.

A Huber pair consists of a Huber ring and a
so-call ring of integral elements: an integrally closed, power bounded, open subring.
A typical example is ℤ_p ⊆ ℚ_p. (However, this example is hard to use as is,
because our fomalisation uses subrings and Lean's version of ℤ_p is not a subring of ℚ_p.
This could be fixed by using injective ring homomorphisms instead of subrings.)

-/

universes u v

open_locale classical
open power_bounded

-- Notation for the power bounded subring
local postfix `ᵒ` : 66 := power_bounded_subring

set_option old_structure_cmd true

/- An subring of a Huber ring is called a “ring of integral elements”
if it is open, integrally closed, and power bounded. See [Wedhorn, Def 7.14].-/
structure is_ring_of_integral_elements (Rplus : Type u) (R : Type u)
  [comm_ring Rplus] [topological_space Rplus] [Huber_ring R] [algebra Rplus R]
  extends is_integrally_closed Rplus R, open_embedding (algebra_map R : Rplus → R) : Prop :=
(is_power_bounded : set.range (algebra_map R : Rplus → R) ≤ Rᵒ)

namespace is_ring_of_integral_elements
variables (Rplus : Type u) (R : Type u)
variables [comm_ring Rplus] [topological_space Rplus] [Huber_ring R] [algebra Rplus R]

lemma plus_is_topological_ring (h : is_ring_of_integral_elements Rplus R) :
  topological_ring Rplus :=
{ continuous_add :=
  begin
    rw h.to_open_embedding.to_embedding.to_inducing.continuous_iff,
    simp only [function.comp, algebra.map_add],
    apply continuous_add,
    all_goals { apply continuous.comp h.to_open_embedding.continuous },
    { exact continuous_fst },
    { exact continuous_snd },
  end,
  continuous_mul :=
  begin
    rw h.to_open_embedding.to_embedding.to_inducing.continuous_iff,
    simp only [function.comp, algebra.map_mul],
    apply continuous_mul,
    all_goals { apply continuous.comp h.to_open_embedding.continuous },
    { exact continuous_fst },
    { exact continuous_snd },
  end,
  continuous_neg :=
  begin
    rw h.to_open_embedding.to_embedding.to_inducing.continuous_iff,
    simp only [function.comp, algebra.map_neg],
    apply continuous_neg,
    exact h.to_open_embedding.continuous,
  end }

end is_ring_of_integral_elements

/-- A Huber pair consists of a Huber ring and a
so-call ring of integral elements: an integrally closed, power bounded, open subring.
(The name “Huber pair” was introduced by Scholze.
Before that, they were called “affinoid rings”.) See [Wedhorn, Def 7.14].-/
structure Huber_pair :=
(plus : Type) -- change this to (Type u) to enable universes
(carrier : Type)
[ring : comm_ring plus]
[top : topological_space plus]
[Huber : Huber_ring carrier]
[alg : algebra plus carrier]
(intel : is_ring_of_integral_elements plus carrier)

namespace Huber_pair
variable (A : Huber_pair)

/-- The coercion of a Huber pair to a type (the ambient ring).-/
instance : has_coe_to_sort Huber_pair :=
{ S := Type, coe := Huber_pair.carrier }

-- The following notation is very common in the literature.
local postfix `⁺` : 66 := λ A : Huber_pair, A.plus

/-- The Huber ring structure on a Huber pair. -/
instance : Huber_ring A := A.Huber

/-- The ring structure on the ring of integral elements. -/
instance : comm_ring (A⁺) := A.ring

/-- The algebra structure of a Huber pair. -/
instance : algebra (A⁺) A := A.alg

/-- The topology on the ring of integral elements. -/
instance : topological_space (A⁺) := A.top

/-- The ring of integral elements is a topological ring.-/
instance : topological_ring (A⁺) :=
is_ring_of_integral_elements.plus_is_topological_ring _ A A.intel

end Huber_pair
