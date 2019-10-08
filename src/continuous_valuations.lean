import topology.algebra.ring
import valuation_spectrum
import valuation.valuation_field_completion

import for_mathlib.nonarchimedean.basic

/-!
# Continuous valuations

The general theory of valuations does not consider a topology on the ring.
However, in practice many rings are naturally topological rings: for example ℝ, ℂ, ℤ_p and ℚ_p.

Among all valuations one can single out a class of “continuous” valuations.
This notions is constant on equivalence classes, and therefore defines a predicate on `Spv R`.

In this file, we introduce this predicate.
-/

universes u u₀ u₁ u₂ u₃

namespace valuation
variables {R : Type u₀} [comm_ring R] [topological_space R]
variables {Γ₀ : Type u} [linear_ordered_comm_group_with_zero Γ₀]
variables {Γ'₀ : Type u₁} [linear_ordered_comm_group_with_zero Γ'₀]
variables {Γ''₀ : Type u₂} [linear_ordered_comm_group_with_zero Γ''₀]
variables {v₁ : valuation R Γ'₀} {v₂ : valuation R Γ''₀}

/-- Continuity of a valuation [Wedhorn 7.7]. -/
def is_continuous (v : valuation R Γ₀) : Prop :=
∀ g : value_monoid v, is_open {r : R | canonical_valuation v r < g}

/-- Continuity of a valuation only depends on its equivalence class. -/
lemma is_equiv.is_continuous_iff (h : v₁.is_equiv v₂) :
  v₁.is_continuous ↔ v₂.is_continuous :=
begin
  unfold valuation.is_continuous,
  rw ← forall_iff_forall_surj (h.value_mul_equiv.to_equiv.bijective.2),
  apply forall_congr,
  intro g,
  convert iff.rfl,
  funext r,
  apply propext,
  rw ← h.with_zero_value_mul_equiv_mk_eq_mk,
  symmetry,
  rw (preorder_equiv.to_lt_equiv h.value_monoid_le_equiv).lt_map,
  exact iff.rfl
end

local attribute [instance] valued.subgroups_basis valued.uniform_space

/-
Mathematical warning:
It is *not true* that v is continuous iff the map R -> Γ₀ is continuous
where Γ₀ gets the usual topology where {γ} and {x < γ} are open, for γ ≠ 0.
What is true is that the valuation is continuous iff the associated map
from R to the valuation field is continuous.
-/

variable [topological_ring R]

/--If R is a topological ring with continuous valuation v, then the natural map from R
to the valuation field of v is continuous.-/
theorem continuous_valuation_field_mk_of_continuous (v : valuation R Γ₀) (hv : is_continuous v) :
  continuous (valuation_field_mk v) :=
topological_add_group.continuous_of_continuous_at_zero (valuation_field_mk v) $
begin
  intros U HU,
  rw is_ring_hom.map_zero (valuation_field_mk v) at HU,
  rcases subgroups_basis.mem_nhds_zero.mp HU with ⟨_, ⟨γ, rfl⟩, Hγ⟩,
  show valuation_field_mk v ⁻¹' U ∈ (nhds (0 : R)),
  let V := {r : R | (canonical_valuation v) r < ↑γ},
  have HV : is_open V := hv γ,
  have H0V : (0 : R) ∈ V,
  { show (canonical_valuation v) 0 < γ,
    rw (canonical_valuation v).map_zero,
    exact linear_ordered_structure.zero_lt_unit _ },
  refine filter.mem_sets_of_superset (mem_nhds_sets HV H0V) _,
  intros u Hu,
  apply set.mem_of_mem_of_subset _ Hγ,
  exact Hu, -- the joys of definitional equality
end

variables {L : Type*} [discrete_field L] [topological_space L] [topological_ring L]

/-- A valuation on a field is continuous if and only if
the sets {y | v y < v x} are open, for all x. -/
lemma is_continuous_iff {v : valuation L Γ₀} :
  v.is_continuous ↔ ∀ x:L, is_open {y:L | v y < v x} :=
begin
  have help : ∀ x:L, value_monoid.to_Γ₀ v (v.canonical_valuation x) = v x,
  { intro x, show v x * (v 1)⁻¹ = v x, by simp },
  split,
  { intros h x,
    specialize h (v.canonical_valuation x),
    simpa only [(value_monoid.to_Γ₀_strict_mono v).lt_iff_lt.symm, help] using h, },
  { intros h x,
    rcases canonical_valuation.surjective v x with ⟨x, rfl⟩,
    simpa only [(value_monoid.to_Γ₀_strict_mono v).lt_iff_lt.symm, help] using h x, }
end

/-- The trivial valuation on a field is continuous if and only if
the topology on the field is discrete. -/
lemma is_continuous_iff_discrete_of_is_trivial (v : valuation L Γ₀) (hv : v.is_trivial) :
  v.is_continuous ↔ discrete_topology L :=
begin
  split; intro h,
  { rw valuation.is_continuous_iff at h,
    suffices : is_open ({(0:L)} : set L),
      from topological_add_group.discrete_iff_open_zero.mpr this,
    specialize h 1,
    rw v.map_one at h,
    suffices : {y : L | v y < 1} = {0}, by rwa this at h,
    ext x,
    rw [set.mem_singleton_iff, ← v.zero_iff],
    show v x < 1 ↔ v x = 0,
    split; intro hx,
    { cases hv x with H H, {assumption},
      { exfalso, rw H at hx, exact lt_irrefl _ hx }, },
    { rw hx, apply lt_of_le_of_ne linear_ordered_structure.zero_le zero_ne_one } },
  { resetI, intro g, exact is_open_discrete _ }
end

end valuation

namespace Spv

variables {R : Type u₀} [comm_ring R] [topological_space R]

/--An equivalence class of valuations is continuous if one representative is continuous.-/
def is_continuous : Spv R → Prop := lift (@valuation.is_continuous _ _ _)

end Spv

variables (R : Type u₁) [comm_ring R] [topological_space R]
variables {Γ₀ : Type u} [linear_ordered_comm_group_with_zero Γ₀]

/--The type of equivalence classes of continuous valuations.-/
def Cont := {v : Spv R | v.is_continuous}

variable {R}

/--A valuation v is continuous if and only if its equivalence class is continuous.-/
lemma mk_mem_Cont (v : valuation R Γ₀) : Spv.mk v ∈ Cont R ↔ v.is_continuous :=
begin
  show Spv.lift (by exactI (λ _ _, by exactI valuation.is_continuous)) (Spv.mk v)
    ↔ valuation.is_continuous v,
  refine (Spv.lift_eq' _ _ _ _),
  intros _ _ _ h,
  resetI,
  exact h.is_continuous_iff,
end

/-- The topology on the space of continuous valuations. -/
instance Cont.topological_space : topological_space (Cont R) := by apply_instance

/-
Wedhorn, p.59 contains the following typo:
  A valuation v on A is continuous if and only if for all γ ∈ Γ₀_v (the value group),
  the set A_{≤γ} := { a ∈ A ; v(a) ≥ γ } is open in A.

  This is a typo, it should be v(a) ≤ γ.
-/
