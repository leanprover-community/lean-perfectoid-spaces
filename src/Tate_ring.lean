import topology.algebra.ring
import ring_theory.subring
import tactic.linarith
import power_bounded
import Huber_ring

-- Scholze : "Recall that a topological ring R is Tate if it contains an
-- open and bounded subring R₀ ⊂ R and a topologically nilpotent unit ϖ ∈ R; such elements are
-- called pseudo-uniformizers."

universe u

variables {R : Type u} [comm_ring R] [topological_space R] [topological_ring R]

open filter function

lemma half_nhds {s : set R} (hs : s ∈ (nhds (0 : R)).sets) :
  ∃ V ∈ (nhds (0 : R)).sets, ∀ v w ∈ V, v * w ∈ s :=
begin
  have : ((λa:R×R, a.1 * a.2) ⁻¹' s) ∈ (nhds ((0, 0) : R × R)).sets :=
    tendsto_mul' (by simpa using hs),
  rw nhds_prod_eq at this,
  rcases filter.mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, filter.inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

def topologically_nilpotent (r : R) : Prop :=
∀ U ∈ (nhds (0 :R)).sets, ∃ N : ℕ, ∀ n : ℕ, n > N → r^n ∈ U

def is_pseudo_uniformizer (ϖ : units R) : Prop := topologically_nilpotent ϖ.val

variable (R)
def pseudo_uniformizer := { ϖ : units R // topologically_nilpotent ϖ.val}


instance pseudo_unif.power_bounded: has_coe (pseudo_uniformizer R) (power_bounded_subring R) :=
⟨λ ⟨ϖ, h⟩, ⟨ϖ, begin
  intros U U_nhds,
  rcases half_nhds U_nhds with ⟨U', ⟨U'_nhds, U'_prod⟩⟩,
  rcases h U' U'_nhds with ⟨N, H⟩,
  let V : set R := (λ u, u*ϖ^(N+1)) '' U',
  have V_nhds : V ∈ (nhds (0 : R)).sets,
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

class Tate_ring (R : Type*) extends comm_ring R, topological_space R, topological_ring R :=
(R₀ : set R)
(R₀_is_open : is_open R₀)
(R₀_is_bounded : is_bounded R₀)
(R₀_is_subring : is_subring R₀)
(ϖ : units R)
(ϖ_is_pseudo_uniformizer : is_pseudo_uniformizer ϖ)

instance tate_ring.to_huber_ring (R : Type*) [Tate_ring R] : Huber_ring R :=
sorry
