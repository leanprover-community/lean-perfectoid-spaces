import ring_theory.power_series
import algebra.char_p

import for_mathlib.nnreal
import for_mathlib.char_p

import valuation.perfection
import perfectoid_space

noncomputable theory
open_locale classical

local postfix `ᵒ` : 66 := power_bounded_subring

section

def nnreal_of_enat (b : nnreal) (n : enat) : nnreal :=
if h : n.dom then (b^n.get h) else 0

@[simp] lemma nnreal_of_enat_top (b : nnreal) :
  nnreal_of_enat b ⊤ = 0 :=
begin
  rw [nnreal_of_enat, dif_neg], exact not_false
end

@[simp] lemma nnreal_of_enat_zero (b : nnreal) :
  nnreal_of_enat b 0 = 1 :=
begin
  rw [nnreal_of_enat, dif_pos, enat.get_zero, pow_zero],
  exact trivial,
end

@[simp] lemma nnreal_of_enat_one (b : nnreal) :
  nnreal_of_enat b 1 = b :=
begin
  rw [nnreal_of_enat, dif_pos, enat.get_one, pow_one],
  exact trivial,
end

@[simp] lemma nnreal_of_enat_add (b : nnreal) (m n : enat) :
  nnreal_of_enat b (m + n) = nnreal_of_enat b m * nnreal_of_enat b n :=
begin
  delta nnreal_of_enat,
  by_cases hm : m.dom,
  { by_cases hn : n.dom,
    { have hmn : (m + n).dom := ⟨hm, hn⟩,
      rw [dif_pos hm, dif_pos hn, dif_pos,
          subtype.coe_ext, nnreal.coe_mul, ← nnreal.coe_mul, ← pow_add, enat.get_add, add_comm],
      exact hmn, },
    { rw [dif_pos hm, dif_neg hn, dif_neg, mul_zero],
      contrapose! hn with H, exact H.2 } },
  { rw [dif_neg hm, dif_neg, zero_mul],
    contrapose! hm with H, exact H.1 },
end

@[simp] lemma nnreal_of_enat_le (b : nnreal) (h₁ : b ≠ 0) (h₂ : b ≤ 1) (m n : enat) (h : m ≤ n) :
  nnreal_of_enat b n ≤ nnreal_of_enat b m :=
begin
  delta nnreal_of_enat,
  by_cases hn : n.dom,
  { rw ← enat.coe_get hn at h,
    have hm : m.dom := enat.dom_of_le_some h,
    rw [← enat.coe_get hm, enat.coe_le_coe] at h,
    rw [dif_pos hm, dif_pos hn],
    rw [← linear_ordered_structure.inv_le_inv one_ne_zero h₁, inv_one'] at h₂,
    have := pow_le_pow h₂ h,
    -- We need lots of norm_cast lemmas
    rwa [nnreal.coe_le, nnreal.coe_pow, nnreal.coe_pow, nnreal.coe_inv, ← pow_inv, ← pow_inv,
      ← nnreal.coe_pow, ← nnreal.coe_pow, ← nnreal.coe_inv, ← nnreal.coe_inv, ← nnreal.coe_le,
      linear_ordered_structure.inv_le_inv] at this,
    all_goals { contrapose! h₁ },
    any_goals { exact subtype.val_injective h₁ },
    all_goals { apply group_with_zero.pow_eq_zero, assumption } },
  { rw dif_neg hn, exact zero_le _ }
end

@[simp] lemma nnreal_of_enat_lt (b : nnreal) (h₁ : b ≠ 0) (h₂ : b < 1) (m n : enat) (h : m < n) :
  nnreal_of_enat b n < nnreal_of_enat b m :=
begin
  delta nnreal_of_enat,
  by_cases hn : n.dom,
  { rw ← enat.coe_get hn at h,
    have hm : m.dom := enat.dom_of_le_some (le_of_lt h),
    rw [← enat.coe_get hm, enat.coe_lt_coe] at h,
    rw [dif_pos hm, dif_pos hn],
    rw [← linear_ordered_structure.inv_lt_inv one_ne_zero h₁, inv_one'] at h₂,
    have := pow_lt_pow h₂ h,
    -- We need lots of norm_cast lemmas
    rwa [nnreal.coe_lt, nnreal.coe_pow, nnreal.coe_pow, nnreal.coe_inv, ← pow_inv, ← pow_inv,
      ← nnreal.coe_pow, ← nnreal.coe_pow, ← nnreal.coe_inv, ← nnreal.coe_inv, ← nnreal.coe_lt,
      linear_ordered_structure.inv_lt_inv] at this,
    all_goals { contrapose! h₁ },
    any_goals { exact subtype.val_injective h₁ },
    all_goals { apply group_with_zero.pow_eq_zero, assumption } },
  { rw dif_neg hn,
    have : n = ⊤ := roption.eq_none_iff'.mpr hn, subst this,
    replace h := ne_of_lt h,
    rw enat.ne_top_iff at h, rcases h with ⟨m, rfl⟩,
    rw dif_pos, swap, {trivial},
    apply pow_pos,
    exact lt_of_le_of_ne b.2 h₁.symm }
end

open function

@[simp] lemma nnreal_of_enat_inj (b : nnreal) (h₁ : b ≠ 0) (h₂ : b < 1) :
  injective (nnreal_of_enat b) :=
begin
  intros m n h,
  wlog H : m ≤ n,
  rcases lt_or_eq_of_le H with H|rfl,
  { have := nnreal_of_enat_lt b h₁ h₂ m n H,
    exfalso, exact ne_of_lt this h.symm, },
  { refl },
end

end

namespace power_series
variables (p : nat.primes)
variables (K : Type*) [discrete_field K] [char_p K p]

def valuation : valuation (power_series K) nnreal :=
{ to_fun := λ φ, nnreal_of_enat (p⁻¹) φ.order,
  map_zero' := by rw [order_zero, nnreal_of_enat_top],
  map_one' := by rw [order_one, nnreal_of_enat_zero],
  map_mul' := λ x y, by rw [order_mul, nnreal_of_enat_add],
  map_add' := λ x y,
  begin
    have : _ ≤ _ := order_add_ge x y,
    rw min_le_iff at this,
    rw le_max_iff,
    have inv_p_ne_zero : (p : nnreal)⁻¹ ≠ 0,
    { assume H, rw [← inv_inj'', inv_inv'', inv_zero'] at H,
      apply p.ne_zero,
      rw [show (p : nnreal) = (p : ℕ), by rw coe_coe] at H, exact_mod_cast H, },
    cases this with h h; [left, right],
    all_goals
    { apply nnreal_of_enat_le _ inv_p_ne_zero _ _ _ h,
      rw [← linear_ordered_structure.inv_le_inv one_ne_zero inv_p_ne_zero, inv_inv'', inv_one'],
      apply le_of_lt,
      rw [show (p : nnreal) = (p : ℕ), by rw coe_coe],
      exact_mod_cast p.one_lt, },
  end }

end power_series

/- The following definition is mathematically correct,
but probably not the version that we want to put into mathlib.
We make it for the sole purpose of constructing a perfectoid field.-/
def laurent_series (K : Type*) [discrete_field K] := localization.fraction_ring (power_series K)

namespace laurent_series
variables (p : nat.primes) (K : Type*) [discrete_field K]

instance : discrete_field (laurent_series K) := by delta laurent_series; apply_instance

def algebra : algebra K (laurent_series K) :=
algebra.of_ring_hom (localization.of ∘ power_series.C K) $
@is_ring_hom.comp _ _ _ _ (power_series.C K) (ring_hom.is_ring_hom _)
  _ _ localization.of localization.of.is_ring_hom

variables [char_p K p]

def valuation : valuation (laurent_series K) nnreal :=
valuation.localization (power_series.valuation p K) $ λ φ h,
begin
  rw localization.fraction_ring.mem_non_zero_divisors_iff_ne_zero at h,
  contrapose! h,
  change nnreal_of_enat _ _ = 0 at h,
  have inv_p_ne_zero : (p : nnreal)⁻¹ ≠ 0,
  { assume H, rw [← inv_inj'', inv_inv'', inv_zero'] at H,
    apply p.ne_zero,
    rw [show (p : nnreal) = (p : ℕ), by rw coe_coe] at H,
    exact_mod_cast H },
  rwa [← nnreal_of_enat_top, (nnreal_of_enat_inj _ inv_p_ne_zero _).eq_iff,
      power_series.order_eq_top] at h,
  rw [← linear_ordered_structure.inv_lt_inv one_ne_zero inv_p_ne_zero, inv_inv'', inv_one'],
  rw [show (p : nnreal) = (p : ℕ), by rw coe_coe],
  exact_mod_cast p.one_lt,
end

lemma non_trivial : ¬ (valuation p K).is_trivial :=
begin
  assume H, cases H (localization.of (power_series.X)) with h h;
  erw valuation.localization_apply at h; change nnreal_of_enat _ _ = _ at h,
  { apply p.ne_zero,
    rw [show (p : nnreal) = (p : ℕ), by rw coe_coe] at h,
    simpa only [nnreal.inv_eq_zero, nnreal_of_enat_one,
      nat.cast_eq_zero, power_series.order_X] using h, },
  { simp only [nnreal_of_enat_one, power_series.order_X] at h,
    rw [← inv_inj'', inv_inv'', inv_one'] at h,
    apply p.ne_one,
    rw [show (p : nnreal) = (p : ℕ), by rw coe_coe] at h,
    exact_mod_cast h }
end

local attribute [instance] algebra

instance : char_p (laurent_series K) (ring_char K) :=
@char_p_algebra K _ _ _ _ _ (ring_char.char _)

end laurent_series

def laurent_series_perfection (K : Type*) [discrete_field K] :=
perfect_closure (laurent_series K) (ring_char K)

namespace laurent_series_perfection
variables (p : nat.primes) (K : Type*) [discrete_field K] [char_p K p]
include p

instance : discrete_field (laurent_series_perfection K) :=
@perfect_closure.discrete_field (laurent_series K) _ _ (ring_char.prime p K) _

def valuation : valuation (laurent_series_perfection K) nnreal :=
@valuation.perfection (laurent_series K) _ (laurent_series.valuation p K)
(ring_char K) (ring_char.prime p _) _

lemma non_discrete (ε : nnreal) (h : 0 < ε) :
  ∃ x : laurent_series_perfection K, 1 < valuation p K x ∧ valuation p K x < 1 + ε :=
@valuation.perfection.non_discrete _ _ _ (ring_char.prime p _) _ _
(laurent_series.non_trivial p K) ε h

lemma non_trivial : ¬ (valuation p K).is_trivial :=
begin
  rcases non_discrete p K 2 (by norm_num) with ⟨x, h₁, h₂⟩,
  contrapose! h₁, cases h₁ x with h h; rw h,
  exact zero_le _,
end

end laurent_series_perfection

namespace laurent_series_perfection
-- Now we take K in universe Type. For example `valued` requires this.
variables (p : nat.primes) (K : Type) [discrete_field K] [char_p K p]
include p

instance : valued (laurent_series_perfection K) :=
{ Γ₀ := nnreal, v := valuation p K }

end laurent_series_perfection

namespace valuation
variables {R : Type*} [comm_ring R]
variables {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]

local attribute [instance] classical.decidable_linear_order

def le_one_subring (v : valuation R Γ₀) := {r : R // v r ≤ 1}

instance le_one_subring.is_subring (v : valuation R Γ₀) : comm_ring v.le_one_subring :=
@subtype.comm_ring R _ {r : R | v r ≤ 1}
{ zero_mem := show v 0 ≤ 1, by simp,
  one_mem := show v 1 ≤ 1, by simp,
  add_mem := λ r s (hr : v r ≤ 1) (hs : v s ≤ 1), show v (r+s) ≤ 1,
  by calc v (r + s) ≤ max (v r) (v s) : v.map_add r s
                ... ≤ 1 : max_le hr hs,
  neg_mem := λ r (hr : v r ≤ 1), show v (-r) ≤ 1, by rwa [v.map_neg],
  mul_mem := λ r s (hr : v r ≤ 1) (hs : v s ≤ 1), show v (r*s) ≤ 1,
  begin
    rw v.map_mul,
    refine le_trans (actual_ordered_comm_monoid.mul_le_mul_right' hr) _,
    rwa one_mul
  end }

end valuation

section pfd_fld
open function
parameter (p : nat.primes)
variables (K : Type) [discrete_field K]

class perfectoid_field : Type :=
[top : uniform_space K]
[top_fld : topological_division_ring K]
[complete : complete_space K]
[sep : separated K]
(v : valuation K nnreal)
(non_discrete : ∀ ε : nnreal, 0 < ε → ∃ x : K, 1 < v x ∧ v x < 1 + ε)
(Frobenius : surjective (Frob v.le_one_subring∕p))

end pfd_fld

section
open uniform_space
variables (p : nat.primes) (K : Type) [discrete_field K] [char_p K p]
include p

local attribute [instance] valued.subgroups_basis subgroups_basis.topology
  ring_filter_basis.topological_ring valued.uniform_space

/-- The completion of the perfection of the Laurent series over a field. -/
def clsp := completion (laurent_series_perfection K)

end

namespace clsp
open uniform_space
variables (p : nat.primes) (K : Type) [discrete_field K] [char_p K p]
include p

local attribute [instance] valued.subgroups_basis subgroups_basis.topology
  ring_filter_basis.topological_ring valued.uniform_space

instance : discrete_field (clsp p K) := completion.discrete_field
instance : uniform_space (clsp p K) := completion.uniform_space _
instance : topological_division_ring (clsp p K) := completion.topological_division_ring
instance : complete_space (clsp p K) := completion.complete_space _
instance : separated (clsp p K) := completion.separated _

def valuation : valuation (clsp p K) nnreal := valued.extension_valuation

instance : perfectoid_field p (clsp p K) :=
{ v := valuation p K,
  non_discrete := λ ε h,
  begin
    choose x hx using laurent_series_perfection.non_discrete p K ε h,
    delta clsp, use x,
    convert hx using 2; exact valued.extension_extends _
  end,
  Frobenius :=
  begin
    apply Frob_mod_surjective_char_p,
    sorry,
    sorry,
  end }

end clsp
