/- 
Copyright (c) 2018 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
Valuation Spectrum 

The valuation spectrum Spv(A) of a (commutative) ring A is the set of all
equivalence classes of valuations on A, equipped with the topology generated
by the sets {v : v(r) <= v(s) != 0} for r,s in A.

IMPORTANT NOTE: Mario says

structure valuations (R : Type) [comm_ring R] :=
{α : Type}
[Hα : linear_ordered_comm_group α]
(f : R → option α)
(Hf : is_valuation f)

should (a) be called valuation and (b) should only have f and Hf in the structure

structure valuation (R : Type) [comm_ring R]
(α : Type) [Hα : linear_ordered_comm_group α] :=
(f : R → option α)
(Hf : is_valuation f)

-/

import valuations 
import analysis.topology.topological_space

definition Spv (A : Type) [comm_ring A] : Type 1 := quotient (valuation.valuations.setoid A)

namespace Spv 

variables {A : Type} [comm_ring A]

open valuation

lemma basic_open.aux1 (r s : A) (v w : valuations A) (H : v ≈ w) :
  v.f(r) ≤ v.f(s) ↔ w.f(r) ≤ w.f(s) := H r s

@[simp] lemma val_zero {α : Type} [linear_ordered_comm_group α] {R : Type} [comm_ring R] 
(f : R → option α) (H : valuation f) : f 0 = 0 := H.map_zero

local attribute [instance] classical.prop_decidable 

lemma basic_open.aux2 (s : A) (v w : valuations A) (H : v ≈ w) :
  v.f(s) > 0 ↔ w.f(s) > 0 := begin
  rw [←not_iff_not],
  rw iff.intro le_of_not_gt not_lt_of_ge,
  rw iff.intro le_of_not_gt not_lt_of_ge,
  rw ←val_zero v.f v.Hf,
  rw ←val_zero w.f w.Hf,
  exact H s 0,
end 

definition basic_open (r s : A) : set (Spv A) := 
  quotient.lift (λ v, valuations.f v r ≤ v.f s ∧ v.f s > 0) (λ v w H,propext begin 
  dsimp,
  rw basic_open.aux1 r s v w H,
  rw basic_open.aux2 s v w H,
  end)
--  (λ v w H, show (v(r) ≤ v(s) ∧ v(s) > 0) ↔ (w(r) ≤ w(s) ∧ w(s) > 0) _

instance (A : Type) [comm_ring A] : topological_space (Spv A) :=
  topological_space.generate_from {U : set (Spv A) | ∃ r s : A, U = basic_open r s}

end Spv
