import topology.algebra.ring
import valuation_spectrum

import for_mathlib.logic

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

/- need :
  1) for all r : R,
  with_zero.map (value_group_equiv h).to_fun (⇑(canonical_valuation v₁) r =
  canonical_valuation v₂ r
  -- This is pulling back a valuation along a map of groups.

  2) with_zero.map (value_group_equiv h) is monotonic. [follows from mono of value_group_equiv]

  3) (follows from 2) it's strictly monotonic. [done: equiv.lt_map_of_le_map]
-/
-- We could probably prove this now, but I didn't do it yet.
lemma is_equiv.is_continuous_iff (h : v₁.is_equiv v₂) :
  v₁.is_continuous ↔ v₂.is_continuous := begin
  unfold valuation.is_continuous,
  rw ←forall_iff_forall_surj (h.value_group_equiv.to_equiv.bijective.2),
  apply forall_congr,
  intro g,
  convert iff.rfl,
  funext r,
  apply propext,
  /-
  ⊢ ⇑(canonical_valuation v₂) r < ↑(⇑((is_equiv.value_group_equiv h).to_equiv) g) ↔
    ⇑(canonical_valuation v₁) r < ↑g
  -/
end
/-
⊢ (∀ (g : value_group v₁), is_open {r : R | ⇑(canonical_valuation v₁) r < ↑g}) ↔
    ∀ (g : value_group v₂), is_open {r : R | ⇑(canonical_valuation v₂) r < ↑g}
-/
/-
begin
  unfold is_continuous,
  split; intros H g,
  { convert H (h.value_group_equiv.symm.to_equiv g),
    symmetry,
    funext,
    apply propext,
    cases classical.em (r ∈ supp v₁),
    { -- comap (quotient.canonical_valuation v) (ideal.quotient.mk (supp v))
      show (quotient.canonical_valuation v₁) (ideal.quotient.mk (supp v₁) r) < _
        ↔ (quotient.canonical_valuation v₂) (ideal.quotient.mk (supp v₂) r) < _,
      rw (ideal.quotient.eq_zero_iff_mem).2 h_1,
      rw (ideal.quotient.eq_zero_iff_mem).2 (h.supp_eq ▸ h_1 : r ∈ supp v₂),
      rw valuation.map_zero,
      rw valuation.map_zero,
      show 0 < some _ ↔ 0 < some _,
      split;intro H; exact with_zero.zero_lt_some,
    },
    { -- goal in this one is to get hold of element of value_group
      -- corresponding to g
     sorry
    }
    rw lt_iff_not_ge,
    rw lt_iff_not_ge,
    apply not_iff_not_of_iff,
    sorry },
  { convert H (h.value_group_equiv.to_equiv g),
    funext,
    apply propext,
    sorry }
end
-/
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

end valuation

namespace Spv
variables {R : Type u₀} [comm_ring R] [topological_space R] [topological_ring R]

def is_continuous : Spv R → Prop := lift (@valuation.is_continuous _ _ _ _)

end Spv

-- KMB has not looked below this point.
#exit
namespace Valuation
variables {R : Type u₁} [comm_ring R] [topological_space R] [topological_ring R] [decidable_eq R]

def is_continuous (v : Valuation R) : Prop := valuation.function_is_continuous v

lemma is_continuous_of_equiv_is_continuous {v₁ v₂ : Valuation R} (heq : v₁ ≈ v₂) (H : v₁.is_continuous) : v₂.is_continuous :=
valuation.is_continuous_of_equiv_is_continuous heq H

end Valuation

namespace Spv

variables {R : Type u₁} [comm_ring R] [topological_space R] [topological_ring R] [decidable_eq R]

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
def Cont := {v : Spv R | (v : Valuation R).is_continuous}
variable {R}

def mk_mem_Cont {v : Valuation R} : mk v ∈ Cont R ↔ v.is_continuous :=
begin
split; intro h; refine Valuation.is_continuous_of_equiv_is_continuous _ h,
exact out_mk, exact (setoid.symm out_mk),
end

instance Cont.topological_space : topological_space (Cont R) := by apply_instance

end Spv

/-
Wedhorn p59:
  A valuation v on A is continuous if and only if for all γ ∈ Γ_v (the value group),
  the set A_{≤γ} := { a ∈ A ; v(a) ≥ γ } is open in A.

  This is a typo -- should be v(a) ≤ γ.
-/
