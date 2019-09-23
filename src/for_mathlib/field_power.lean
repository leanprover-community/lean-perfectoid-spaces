import tactic.linarith
import algebra.field_power -- PR the current file to that one

section ordered
variables  {α : Type*} [discrete_linear_ordered_field α]

lemma nat.fpow_pos_of_pos {p : ℕ} (h : 0 < p) (n:ℤ) : (p:α)^n > 0 :=
by { apply fpow_pos_of_pos, exact_mod_cast h }

lemma nat.fpow_ne_zero_of_pos {p : ℕ} (h : 0 < p) (n:ℤ) : (p:α)^n ≠ 0 :=
ne_of_gt (nat.fpow_pos_of_pos h n)

lemma fpow_strict_mono {x : α} (hx : 1 < x) :
  strict_mono (λ n:ℤ, x ^ n) :=
λ m n h, show x ^ m < x ^ n,
begin
  have xpos : 0 < x := by linarith,
  have h₀ : x ≠ 0 := by linarith,
  have hxm : 0 < x^m := fpow_pos_of_pos xpos m,
  have hxm₀ : x^m ≠ 0 := ne_of_gt hxm,
  suffices : 1 < x^(n-m),
  { replace := mul_lt_mul_of_pos_right this hxm,
    simpa [*, fpow_add, mul_assoc, fpow_neg, inv_mul_cancel], },
  apply one_lt_fpow hx, linarith,
end

@[simp] lemma fpow_mono {x : α} (hx : 1 < x) {m n : ℤ} :
  x ^ m < x ^ n ↔ m < n :=
(fpow_strict_mono hx).lt_iff_lt

@[simp] lemma fpow_inj {x : α} (h₀ : 0 < x) (h₁ : x ≠ 1) {m n : ℤ} :
  x ^ m = x ^ n ↔ m = n :=
begin
  split; intro h, swap, {simp [h]},
  rcases lt_trichotomy x 1 with H|rfl|H,
  { apply (fpow_strict_mono (one_lt_inv h₀ H)).injective,
    show x⁻¹ ^ m = x⁻¹ ^ n,
    rw [← fpow_inv, ← fpow_mul, ← fpow_mul, mul_comm _ m, mul_comm _ n, fpow_mul, fpow_mul, h], },
  { contradiction },
  { exact (fpow_strict_mono H).injective h, },
end
end ordered


@[simp] theorem fpow_neg_mul_fpow_self {α : Type*} [discrete_field α] (n : ℕ) {x : α} (h : x ≠ 0) :
  x^-(n:ℤ) * x^n = 1 :=
begin
  convert inv_mul_cancel (pow_ne_zero n h),
  rw [fpow_neg, one_div_eq_inv, fpow_of_nat]
end

@[simp, move_cast] theorem cast_fpow {α : Type*} [discrete_field α] [char_zero α] (q : ℚ) (k : ℤ) :
  ((q ^ k : ℚ) : α) = q ^ k :=
begin
  cases k,
  { erw fpow_of_nat,
    rw rat.cast_pow,
    erw fpow_of_nat },
  { rw fpow_neg_succ_of_nat,
    rw fpow_neg_succ_of_nat,
    norm_cast }
end
