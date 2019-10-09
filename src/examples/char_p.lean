import ring_theory.power_series
import algebra.char_p

import for_mathlib.nnreal

import adic_space

section

open_locale classical

noncomputable def nnreal_of_enat (b : nnreal) (n : enat) : nnreal :=
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

end

namespace power_series
variables {p : ℕ} [hp : p.prime]
variables {K : Type*} [discrete_field K] [char_p K p]
include hp

open_locale classical

noncomputable def valuation : valuation (power_series K) nnreal :=
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
      apply hp.ne_zero, exact_mod_cast H },
    cases this with h h; [left, right],
    all_goals
    { apply nnreal_of_enat_le _ inv_p_ne_zero _ _ _ h,
      rw [← linear_ordered_structure.inv_le_inv one_ne_zero inv_p_ne_zero, inv_inv'', inv_one'],
      exact_mod_cast le_of_lt hp.one_lt, },
  end }

end power_series
