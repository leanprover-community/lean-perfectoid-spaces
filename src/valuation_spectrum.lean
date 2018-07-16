/- 
Copyright (c) 2018 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
Valuation Spectrum 

The valuation spectrum Spv(A) of a (commutative) ring A is the set of all
equivalence classes of valuations on A, equipped with the topology generated
by the sets {v : v(r) <= v(s) != 0} for r,s in A.

-/

import valuations 
import analysis.topology.topological_space

definition Spv (A : Type) [comm_ring A] : Type 1 := quotient (valuations.setoid A)

namespace Spv 

variables {A : Type} [comm_ring A] -- fix a ring A

local attribute [instance] classical.prop_decidable

-- Should this lemma be in the file valuations.lean ??
lemma gt_zero_iff_equiv_gt_zero (s : A) (v w : valuations A) (H : v ≈ w) :
v(s) > 0 ↔ w(s) > 0 :=
begin
  rw [←not_iff_not,
      iff.intro le_of_not_gt not_lt_of_ge,
      iff.intro le_of_not_gt not_lt_of_ge,
      ←v.Hf.map_zero,
      ←w.Hf.map_zero],
  exact H s 0,
end 

/-- The basic open subset for the topology on Spv(A).-/
definition basic_open (r s : A) : set (Spv A) :=
-- on representatives
quotient.lift (λ v : valuations A, v(r) ≤ v(s) ∧ v(s) > 0)
-- independence of representative
  (λ v w H,
  begin
    dsimp,
    rw [H r s, gt_zero_iff_equiv_gt_zero s v w H]
  end)

instance (A : Type) [comm_ring A] : topological_space (Spv A) :=
topological_space.generate_from {U : set (Spv A) | ∃ r s : A, U = basic_open r s}

end Spv
