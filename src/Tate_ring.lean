import topology.algebra.ring
import ring_theory.subring
import tactic.linarith
import power_bounded
import Huber_ring.basic

import for_mathlib.topological_rings

-- Scholze : "Recall that a topological ring R is Tate if it contains an
-- open and bounded subring R₀ ⊂ R and a topologically nilpotent unit ϖ ∈ R; such elements are
-- called pseudo-uniformizers."

-- jmc: Shall we remove the above quote?
-- jmc: We define Tate ring as a Huber ring with a pseudo-uniformizer.

universe u

variables {R : Type u} [comm_ring R] [topological_space R] [topological_ring R]

open filter function

def is_pseudo_uniformizer (ϖ : units R) : Prop := is_topologically_nilpotent ϖ.val

variable (R)
def pseudo_uniformizer := { ϖ : units R // is_topologically_nilpotent ϖ.val}

instance pseudo_uniformizer.power_bounded :
  has_coe (pseudo_uniformizer R) (power_bounded_subring R) :=
⟨λ ⟨ϖ, h⟩, ⟨ϖ, begin
  intros U U_nhds,
  rcases half_nhds U_nhds with ⟨U', ⟨U'_nhds, U'_prod⟩⟩,
  rcases h U' U'_nhds with ⟨N, H⟩,
  let V : set R := (λ u, u*ϖ^(N+1)) '' U',
  have V_nhds : V ∈ (nhds (0 : R)),
  { dsimp [V],
    have inv : left_inverse (λ (u : R), u * (↑ϖ⁻¹)^((N + 1))) (λ (u : R), u * ϖ^(N + 1)) ∧
        right_inverse (λ (u : R), u * (↑ϖ⁻¹)^(N + 1)) (λ (u : R), u * ϖ^(N + 1)),
    by split ; intro ; simp [mul_assoc, (mul_pow _ _ _).symm],
    rw set.image_eq_preimage_of_inverse inv.1 inv.2,
    have : tendsto (λ (u : R), u * ↑ϖ⁻¹ ^ (N + 1)) (nhds 0) (nhds 0),
    { conv {congr, skip, skip, rw ←(zero_mul (↑ϖ⁻¹ ^ (N + 1) : R))},
        exact tendsto_mul tendsto_id tendsto_const_nhds },
    exact this U'_nhds },
  use [V, V_nhds],
  rintros v ⟨u, u_in, uv⟩ b ⟨n, h'⟩,
  rw [← h', ←uv, mul_assoc, ← pow_add],
  apply U'_prod _ _ u_in (H _ _),
  clear uv h', -- otherwise linarith gets confused
  linarith
end⟩⟩

class Tate_ring (R : Type u) [Huber_ring R] : Prop :=
(has_pseudo_uniformizer : ∃ ϖ : units R, is_pseudo_uniformizer ϖ)
