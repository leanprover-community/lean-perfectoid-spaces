import topology.algebra.ring
import valuation_spectrum
import valuation.valuation_field_completion -- for valuation top on K_v

import for_mathlib.nonarchimedean.basic -- continuous_of_continuous_at_zero

universes u u₀ u₁ u₂ u₃

namespace valuation
variables {R : Type u₀} [comm_ring R] [topological_space R] [topological_ring R]
variables {Γ : Type u} [linear_ordered_comm_group Γ]
variables {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]
variables {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂}

/-- Continuity of a valuation (Wedhorn 7.7). -/
def is_continuous (v : valuation R Γ) : Prop :=
∀ g : value_group v, is_open {r : R | canonical_valuation v r < g}

lemma is_equiv.is_continuous_iff (h : v₁.is_equiv v₂) :
  v₁.is_continuous ↔ v₂.is_continuous := begin
  unfold valuation.is_continuous,
  rw ←forall_iff_forall_surj (h.value_mul_equiv.to_equiv.bijective.2),
  apply forall_congr,
  intro g,
  convert iff.rfl,
  funext r,
  apply propext,
  rw h.with_zero_value_group_lt_equiv.lt_map,
  convert iff.rfl,
  exact h.with_zero_value_mul_equiv_mk_eq_mk r,
end

/- Alternative def which KMB has now commented out.

-- jmc: Is this definition equivalent?
-- KMB: I guess so. The extra edge cases are s₁ or s₂ in supp(v)
-- and in these cases the modified definition is furthermore asking
-- that the empty set and the whole ring are open, but
-- both of these are always true.
-- The value group is Frac(R/supp(v))^* hence everything in it
-- is represented by s₂/s₁, so it boils down to checking that
-- x * some(g) < some(h) iff x < some(h/g). This is true for x=0
-- and also true for x=some(k) (it follows from the axiom)
-- although I glanced through the API
-- and couldn't find it.

def is_continuous' (v : valuation R Γ) : Prop :=
∀ s₁ s₂, is_open {r : R | v r * v s₁ < v s₂}

-- KMB never finished this and I don't think we need it any more.
lemma continuous_iff_continuous' {v : valuation R Γ} :
is_continuous' v ↔ is_continuous v :=
begin
  split,
  { intro h,
    rintro ⟨⟨r,s⟩,u',huu',hu'u⟩,
    --have := h s.val r,
    --dsimp,
    sorry
  },
  {
    sorry
  }
end


lemma is_equiv.is_continuous'_iff (h : v₁.is_equiv v₂) :
  v₁.is_continuous' ↔ v₂.is_continuous' :=
begin
  apply forall_congr,
  intro s₁,
  apply forall_congr,
  intro s₂,
  convert iff.rfl,
  symmetry,
  funext,
  rw [lt_iff_le_not_le, lt_iff_le_not_le],
  apply propext,
  apply and_congr,
  { rw [← map_mul v₁, ← map_mul v₂],
    apply h },
  { apply not_iff_not_of_iff,
    rw [← map_mul v₁, ← map_mul v₂],
    apply h }
end
-/

local attribute [instance] valued.subgroups_basis valued.uniform_space

-- It is *not true* that v is continuous iff the map R -> with_zero Γ is continuous
-- where with_zero Γ gets the usual topology where {γ} and {x < γ} are open. What is
-- true is that the valuation is continuous iff the associated map from R to the
-- valuation field is continuous.

lemma continuous_valuation_field_mk_at_zero (v : valuation R Γ) (hv : is_continuous v) :
continuous_at (valuation_field_mk v) 0 :=
begin
  intros U HU,
  conv at HU in (valuation_field_mk v 0) begin
    rw is_ring_hom.map_zero (valuation_field_mk v),
  end,
  rcases subgroups_basis.mem_nhds_zero.mp HU with ⟨_, ⟨γ, rfl⟩, Hγ⟩,
  show valuation_field_mk v ⁻¹' U ∈ (nhds (0 : R)),
  let V := {r : R | (canonical_valuation v) r < ↑γ},
  have HV : is_open V := hv γ,
  have H0V : (0 : R) ∈ V,
    show (canonical_valuation v) 0 < γ,
    rw (canonical_valuation v).map_zero,
    exact with_zero.zero_lt_coe,
  refine filter.mem_sets_of_superset (mem_nhds_sets HV H0V) _,
  intros u Hu,
  apply set.mem_of_mem_of_subset _ Hγ,
  exact Hu, -- the joys of definitional equality
end

theorem continuous_valuation_field_mk_of_continuous (v : valuation R Γ) (hv : is_continuous v) :
  continuous (valuation_field_mk v) :=
topological_add_group.continuous_of_continuous_at_zero (valuation_field_mk v) $
  continuous_valuation_field_mk_at_zero v hv

end valuation

namespace Spv

variables {R : Type u₀} [comm_ring R] [topological_space R] [topological_ring R]

def is_continuous : Spv R → Prop := lift (@valuation.is_continuous _ _ _ _)

end Spv

/- KMB proposes removing Valuation completely because of universe issues

namespace Valuation
variables {R : Type u₁} [comm_ring R] [topological_space R] [topological_ring R] [decidable_eq R]

def is_continuous (v : Valuation R) : Prop := valuation.function_is_continuous v

lemma is_continuous_of_equiv_is_continuous {v₁ v₂ : Valuation R} (heq : v₁ ≈ v₂) (H : v₁.is_continuous) : v₂.is_continuous :=
valuation.is_continuous_of_equiv_is_continuous heq H

end Valuation

-/

namespace Spv

variables {R : Type u₁} [comm_ring R] [topological_space R] [topological_ring R] [decidable_eq R]
variables {Γ : Type u} [linear_ordered_comm_group Γ]

/-
theorem forall_continuous {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]
  (vs : Spv R) : Spv.is_continuous vs ↔ ∀ (Γ : Type*) [linear_ordered_comm_group Γ],
  by exactI ∀ (v : valuation R Γ), (∀ r s : R, vs.val r s ↔ v r ≤ v s) → valuation.is_continuous v :=
begin
  split,
  { intros Hvs Γ iΓ v Hv,
    cases Hvs with Δ HΔ,
    cases HΔ with iΔ HΔ,
    cases HΔ with w Hw,
    -- this is the hard part
    -- our given w is continuous -> all v are continuous
    intros g Hg,
    sorry
  },
  { intro H,
    cases vs with ineq Hineq,
    cases Hineq with Γ HΓ,
    cases HΓ with iΓ HΓ,
    cases HΓ with v Hv,
    unfold is_continuous,
    existsi Γ,
    existsi iΓ,
    existsi v,
    split,
      exact Hv,
    apply H,
    exact Hv
  }
end
-/

variable (R)

def Cont := {v : Spv R | v.is_continuous}

variable {R}

def mk_mem_Cont {v : valuation R Γ} : mk v ∈ Cont R ↔ v.is_continuous :=
begin
  show Spv.lift (by exactI (λ _ _, by exactI valuation.is_continuous)) (Spv.mk v)
    ↔ valuation.is_continuous v,
  refine (lift_eq' _ _ _ _),
  intros _ _ _ h,
  resetI,
  exact h.is_continuous_iff,
end

instance Cont.topological_space : topological_space (Cont R) := by apply_instance

end Spv

/-
Wedhorn p59:
  A valuation v on A is continuous if and only if for all γ ∈ Γ_v (the value group),
  the set A_{≤γ} := { a ∈ A ; v(a) ≥ γ } is open in A.

  This is a typo -- should be v(a) ≤ γ. [KMB agrees]
-/
