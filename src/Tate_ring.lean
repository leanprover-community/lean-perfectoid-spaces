import topology.algebra.ring
import ring_theory.subring
import tactic.linarith
import power_bounded
import Huber_ring.basic

import for_mathlib.topological_rings

/-!
# Tate rings

A Tate ring is a Huber ring that has a topologically nilpotent unit.
Topologically nilpotent units are also called pseudo-uniformizers.
-/

universe u

variables {R : Type u} [comm_ring R] [topological_space R]

open filter function

/--A unit of a topological ring is called a pseudo-uniformizer if it is topologically nilpotent.-/
def is_pseudo_uniformizer (ϖ : units R) : Prop := is_topologically_nilpotent (ϖ : R)

variable (R)
/--A pseudo-uniformizer of a topological ring is a topologially nilpotent unit.-/
def pseudo_uniformizer := {ϖ : units R // is_topologically_nilpotent (ϖ : R)}
variable {R}

namespace pseudo_uniformizer

/-- The coercion from pseudo-uniformizers to the unit group. -/
instance : has_coe (pseudo_uniformizer R) (units R) := ⟨subtype.val⟩

/--The unit underlying a pseudo-uniformizer.-/
abbreviation unit (ϖ : pseudo_uniformizer R) : units R := ϖ

/--A pseudo-uniformizer is topologically nilpotent (by definition).-/
lemma is_topologically_nilpotent (ϖ : pseudo_uniformizer R) :
  is_topologically_nilpotent (ϖ : R) := ϖ.property

variables [topological_ring R]

/--A pseudo-uniformizer is power bounded.-/
lemma power_bounded (ϖ : pseudo_uniformizer R) :
  is_power_bounded (ϖ : R) :=
begin
  intros U U_nhds,
  rcases half_nhds U_nhds with ⟨U', ⟨U'_nhds, U'_prod⟩⟩,
  rcases ϖ.is_topologically_nilpotent U' U'_nhds with ⟨N, H⟩,
  let V : set R := (λ u, u*ϖ^(N+1)) '' U',
  have V_nhds : V ∈ (nhds (0 : R)),
  { dsimp [V],
    have inv : left_inverse (λ (u : R), u * (↑ϖ.unit⁻¹)^((N + 1))) (λ (u : R), u * ϖ^(N + 1)) ∧
        right_inverse (λ (u : R), u * (↑ϖ.unit⁻¹)^(N + 1)) (λ (u : R), u * ϖ^(N + 1)),
    by split ; intro ; simp [mul_assoc, (mul_pow _ _ _).symm],
    erw set.image_eq_preimage_of_inverse inv.1 inv.2,
    have : tendsto (λ (u : R), u * ↑ϖ.1⁻¹ ^ (N + 1)) (nhds 0) (nhds 0),
    { conv {congr, skip, skip, rw ←(zero_mul (↑ϖ.1⁻¹ ^ (N + 1) : R))},
        exact tendsto.mul tendsto_id tendsto_const_nhds },
    exact this U'_nhds },
  use [V, V_nhds],
  rintros _ ⟨u, u_in, rfl⟩ b ⟨n, rfl⟩,
  rw [mul_assoc, ← pow_add],
  apply U'_prod _ _ u_in (H _ _),
  linarith
end

/-- The coercion from pseudo-uniformizers to the power bounded subring. -/
instance coe_to_power_bounded_subring : has_coe (pseudo_uniformizer R) (power_bounded_subring R) :=
⟨λ ϖ, ⟨_, ϖ.power_bounded⟩⟩

end pseudo_uniformizer

/--A Tate ring is a Huber ring that has a pseudo uniformizer.-/
class Tate_ring (R : Type u) [Huber_ring R] : Prop :=
(has_pseudo_uniformizer : nonempty (pseudo_uniformizer R))
