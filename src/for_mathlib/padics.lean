-- If we PR this to mathlib, we probably need to split things in
-- padic_numbers and padic_int

import data.padics

import for_mathlib.adic_topology

local attribute [simp] nat.prime.ne_zero

namespace padic_numbers

variables {p : ℕ} [nat.prime p]

@[simp] lemma norm_p : ∥(p : ℚ_[p])∥ = p⁻¹ := sorry
@[simp] lemma norm_nat_pow_p (n : ℕ) : ∥(p : ℚ_[p])^n∥ = (p : ℝ) ^ (-n : ℤ) := sorry
@[simp] lemma norm_int_pow_p (n : ℤ) : ∥(p : ℚ_[p])^n∥ = (p : ℝ) ^ -n := sorry

@[simp] lemma p_ne_zero : (p : ℚ_[p]) ≠ 0 :=
by simpa [-padic.cast_eq_of_rat_of_nat] using nat.prime.ne_zero ‹p.prime›

end padic_numbers

namespace padic_int
open function

variables {p : ℕ} [nat.prime p]

@[simp] lemma norm_p : ∥(p : ℤ_[p])∥ = p⁻¹ := sorry
@[simp] lemma norm_pow_p (n : ℕ) : ∥(p : ℤ_[p])^n∥ = (p : ℝ) ^ (-n : ℤ) := sorry
@[simp] lemma norm_units (u : units ℤ_[p]) : ∥(u : ℤ_[p])∥ = 1 :=
is_unit_iff.mp $ is_unit_unit u

@[simp] lemma coe_nat_val (n : ℕ) : ((n : ℤ_[p]) : ℚ_[p]) = n :=
by induction n; simp [*]

@[simp] lemma coe_int_val (n : ℤ) : ((n : ℤ_[p]) : ℚ_[p]) = n :=
by cases n; simp

@[simp] lemma p_ne_zero : (p : ℤ_[p]) ≠ 0 :=
λ h, by rw [subtype.coe_ext] at h; simpa [-padic.cast_eq_of_rat_of_nat] using h

open padic_norm_z padic_val_rat

lemma image {x : ℤ_[p]} : x ≠ 0 → ∃ n : ℕ, ∥x∥ = p ^ (-n : ℤ) :=
begin
  intro h,
  erw ← padic_norm_e_of_padic_int,
  have h' : (x : ℚ_[p]) ≠ 0 :=
  begin
    intro H,
    rw [← coe_zero, ← subtype.coe_ext] at H,
    exact h H,
  end,
  cases padic_norm_e.image h' with n hn,
  rw hn,
  use int.nat_abs n,
  have n_ge : n ≥ 0 :=
  begin
    have hx := x.property,
    erw [hn] at hx,
    by_contradiction H,
    apply not_lt_of_le hx,
    rw [not_le, ← neg_lt_neg_iff, neg_zero] at H,
    have : (1 : ℚ) < p :=
    by { rw [← nat.cast_one, nat.cast_lt], apply nat.prime.gt_one, assumption },
    convert rat.cast_lt.mpr (one_lt_fpow this _ H),
    simp,
  end,
  rw [fpow_neg, fpow_neg, one_div_eq_inv, one_div_eq_inv, rat.cast_inv],
  congr,
  conv {to_lhs, rw [← (abs_of_nonneg n_ge), int.abs_eq_nat_abs]},
  erw [fpow_of_nat, fpow_of_nat],
  simp,
end

lemma repr {x : ℤ_[p]} (hx : x ≠ 0) : ∃ (n : ℕ) (u : units ℤ_[p]), x = u * p^n :=
begin
  cases image hx with n hn,
  have hu : ∥(x : ℚ_[p]) * p ^ (-n : ℤ)∥ = 1 :=
  begin
    erw [padic_norm_e.mul, hn, padic_numbers.norm_int_pow_p (-n)],
    erw ← fpow_add,
    { simp },
    simpa [-padic.cast_eq_of_rat_of_nat] using nat.prime.ne_zero ‹p.prime›
  end,
  choose u H using (@is_unit_iff _ _ ⟨_, le_of_eq hu⟩).mpr hu,
  use [n, u],
  rw ← H,
  apply subtype.val_injective,
  simp [-padic.cast_eq_of_rat_of_nat],
  erw [mul_assoc, ← fpow_of_nat, ← fpow_add];
    simp [-padic.cast_eq_of_rat_of_nat],
end

/-
jmc: HELP!!!
subtype.metric_space seems to be missing
-/

noncomputable instance : metric_space ℤ_[p] := sorry -- subtype.metric_space

lemma neg_def : ∀ x : ℤ_[p], -x = ⟨-x.val, by cases x; simpa⟩
| ⟨x, hx⟩ := rfl

instance : topological_ring ℤ_[p] :=
{ continuous_neg :=
  begin
    suffices : continuous (λ (x : ℤ_[p]), show ℤ_[p], from ⟨-x.val, by cases x; simpa⟩),
    { simpa [neg_def] },
    apply continuous_subtype_mk,
    apply continuous_neg continuous_subtype_val,
    apply_instance
  end,
  continuous_add :=
  begin
    suffices : continuous (λ (x : ℤ_[p] × ℤ_[p]), show ℤ_[p], from ⟨x.fst + x.snd, _⟩),
    { convert this,
      { funext, apply subtype.val_injective, simp [add_def] },
      refine le_trans (padic_norm_e.nonarchimedean _ _) (max_le_iff.2 _),
      cases x with x y, cases x, cases y, split; assumption },
    apply continuous_subtype_mk,
    apply continuous_add
      (continuous_fst.comp continuous_subtype_val)
      (continuous_snd.comp continuous_subtype_val),
    apply_instance
  end,
  continuous_mul :=
  begin
    suffices : continuous (λ (x : ℤ_[p] × ℤ_[p]), show ℤ_[p], from ⟨x.fst * x.snd, _⟩),
    { convert this,
      { funext, apply subtype.val_injective, simp [add_def] },
      begin rw padic_norm_e.mul, apply mul_le_one;
        { cases x with x y, cases x, cases y,
          assumption <|> apply norm_nonneg }
      end },
    apply continuous_subtype_mk,
    apply continuous_mul
      (continuous_fst.comp continuous_subtype_val)
      (continuous_snd.comp continuous_subtype_val),
    apply_instance
  end }

instance coe_is_ring_hom : is_ring_hom (λ x, x : ℤ_[p] → ℚ_[p]) :=
by refine {..} ; intros ; simp

lemma nonunits_ideal_eq :
  (nonunits_ideal padic_int.is_local_ring : ideal ℤ_[p]) = ideal.span {p} :=
begin
  apply le_antisymm,
  { intro x,
    erw [mem_nonunits, ideal.mem_span_singleton],
    by_cases h : x = 0,
    { simp [h] },
    rcases repr h with ⟨n, u, H⟩,
    rw H,
    intro hle,
    cases n,
    { exfalso,
      simp at hle,
      apply not_lt.mpr (le_refl _) hle },
    { rw [pow_succ', ← mul_assoc],
      apply dvd_mul_of_dvd_right,
      exact dvd_refl _ } },
  { erw [ideal.span_le, set.singleton_subset_iff, mem_nonunits, ← padic_norm_e_of_padic_int,
      padic_int.coe_coe, padic.cast_eq_of_rat_of_nat, padic_norm_e.eq_padic_norm, padic_norm],
    split_ifs,
    { simp [zero_lt_one] },
    { replace h := nat.prime.gt_one ‹p.prime›,
      erw padic_val_rat_self h,
      erw [fpow_neg, fpow_of_nat, pow_one, one_div_eq_inv, rat.cast_inv, rat.cast_coe_nat],
      apply inv_lt_one,
      rwa [← nat.cast_one, nat.cast_lt] } }
end

lemma span_pow_eq (n : ℕ) :
  (ideal.span {(p^n : ℤ_[p])}).carrier = metric.ball (0 : ℤ_[p]) (p^ (-n : ℤ)) :=
sorry

lemma is_open_pow_nonunits_ideal (n : ℕ) :
  is_open ((nonunits_ideal padic_int.is_local_ring : ideal ℤ_[p])^n).carrier :=
begin
  rw nonunits_ideal_eq,
  sorry
  -- rw pow_span_eq, -- doesn't exist yet
  -- rw span_pow_eq,
  -- exact metric.is_open_ball
end

lemma is_p_adic : is_ideal_adic (nonunits_ideal padic_int.is_local_ring : ideal ℤ_[p]) :=
begin
  rw is_ideal_adic_iff,
  split,
  { exact is_open_pow_nonunits_ideal, },
  { intros s hs,
    rw metric.mem_nhds_iff at hs,
    rcases hs with ⟨ε, Hε, H⟩,
    -- find n such that p^(-n) < ε,
    -- now use span_pow_eq and Hε,
    sorry }
end

end padic_int
