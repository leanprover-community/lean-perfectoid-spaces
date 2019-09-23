import data.padics
import Huber_ring.basic
import for_mathlib.field_power

noncomputable theory
open_locale classical

variables {p : ℕ} [nat.prime p]

local attribute [-simp] padic.cast_eq_of_rat_of_nat

lemma ideal.one_mem_of_unit_mem {R : Type*} [comm_ring R] {I : ideal R} {u : units R} (h : (u : R) ∈ I) :
(1 : R) ∈ I :=
begin
  have : (u : R)*(u⁻¹ : units R) ∈ I, from I.mul_mem_right h,
  rwa u.mul_inv at this
end

lemma ideal.span_singleton_mul {R : Type*} [comm_ring R] (x y : R) :
(ideal.span ({x} : set R)) * (ideal.span {y}) = ideal.span {x*y} :=
by simp [ideal.span_mul_span]

lemma ideal.span_singleton_pow {R : Type*} [comm_ring R] (x : R) (n : ℕ) :
(ideal.span ({x} : set R))^n = ideal.span {x^n} :=
begin
  induction n with n ih,
  { simp },
  { rw [pow_succ, ih, ideal.span_singleton_mul, pow_succ] }
end

-- This should be generalised in 10 directions

namespace padic_seq

def valuation (f : padic_seq p) : ℤ :=
if hf : f ≈ 0 then 0 else padic_val_rat p (f (stationary_point hf))

lemma norm_eq_pow_val {f : padic_seq p} (hf : ¬ f ≈ 0) :
  f.norm = p^(-f.valuation : ℤ) :=
begin
  delta norm valuation,
  rw [dif_neg hf, dif_neg hf],
  delta padic_norm,
  rw if_neg,
  assume H, apply cau_seq.not_lim_zero_of_not_congr_zero hf,
  intros ε hε,
  use (stationary_point hf),
  intros n hn,
  rw stationary_point_spec hf (le_refl _) hn,
  simpa [H] using hε,
end

lemma val_eq_iff_norm_eq {f g : padic_seq p} (hf : ¬ f ≈ 0) (hg : ¬ g ≈ 0) :
  f.valuation = g.valuation ↔ f.norm = g.norm :=
begin
  rw [norm_eq_pow_val hf, norm_eq_pow_val hg, ← neg_inj', fpow_inj],
  { exact_mod_cast nat.prime.pos ‹_› },
  { exact_mod_cast nat.prime.ne_one ‹_› },
end

end padic_seq

namespace padic

@[simp] lemma norm_p : ∥(p : ℚ_[p])∥ = p⁻¹ :=
begin
  have p₀ : p ≠ 0 := nat.prime.ne_zero ‹_›,
  have p₁ : p ≠ 1 := nat.prime.ne_one ‹_›,
  simp [p₀, p₁, norm, padic_norm, padic_val_rat, fpow_neg, padic.cast_eq_of_rat_of_nat],
end

@[simp] lemma norm_p_pow (n : ℤ) : ∥(p^n : ℚ_[p])∥ = p^-n :=
by rw [norm_fpow, norm_p, fpow_neg, one_div_eq_inv,
  ← fpow_inv, ← fpow_inv, ← fpow_mul, ← fpow_mul, mul_comm]

def valuation : ℚ_[p] → ℤ :=
quotient.lift (@padic_seq.valuation p _) (λ f g h,
begin
  by_cases hf : f ≈ 0,
  { have hg : g ≈ 0, from setoid.trans (setoid.symm h) hf,
    simp [hf, hg, padic_seq.valuation] },
  { have hg : ¬ g ≈ 0, from (λ hg, hf (setoid.trans h hg)),
    rw padic_seq.val_eq_iff_norm_eq hf hg,
    exact padic_seq.norm_equiv h },
end)

@[simp] lemma valuation_zero : valuation (0 : ℚ_[p]) = 0 :=
dif_pos ((const_equiv p).2 rfl)

@[simp] lemma valuation_one : valuation (1 : ℚ_[p]) = 0 :=
begin
  change dite (cau_seq.const (padic_norm p) 1 ≈ _) _ _ = _,
  have h : ¬ cau_seq.const (padic_norm p) 1 ≈ 0,
  { assume H, erw const_equiv p at H, exact one_ne_zero H },
  rw dif_neg h,
  simp,
end

lemma norm_eq_pow_val {x : ℚ_[p]} (hx : x ≠ 0) :
  ∥x∥ = p^(-x.valuation) :=
begin
  revert hx, apply quotient.induction_on' x, clear x,
  intros f hf,
  change (padic_seq.norm _ : ℝ) = (p : ℝ) ^ -padic_seq.valuation _,
  rw padic_seq.norm_eq_pow_val,
  change ↑((p : ℚ) ^ -padic_seq.valuation f) = (p : ℝ) ^ -padic_seq.valuation f,
  { rw cast_fpow,
    congr' 1,
    norm_cast },
  { apply cau_seq.not_lim_zero_of_not_congr_zero,
    contrapose! hf, apply quotient.sound, simpa using hf, }
end

@[simp] lemma valuation_p : valuation (p : ℚ_[p]) = 1 :=
begin
  have h : (1 : ℝ) < p := by exact_mod_cast nat.prime.one_lt ‹_›,
  apply neg_inj,
  apply (fpow_strict_mono h).injective,
  dsimp only,
  rw ← norm_eq_pow_val,
  { simp [fpow_inv], },
  { exact_mod_cast nat.prime.ne_zero ‹_›, }
end

end padic

namespace padic_int
open local_ring

lemma norm_mul (x y : ℤ_[p]) : ∥x*y∥ = ∥x∥*∥y∥ :=
by exact_mod_cast norm_mul (x:ℚ_[p]) (y:ℚ_[p])

lemma norm_pow (x : ℤ_[p]) : ∀ (n : ℕ), ∥x^n∥ = ∥x∥^n
| 0     := by simp
| (n+1) := by simp

@[simp] lemma norm_p : ∥(p : ℤ_[p])∥ = p⁻¹ :=
show ∥((p : ℤ_[p]) : ℚ_[p])∥ = p⁻¹, by exact_mod_cast padic.norm_p

@[simp] lemma norm_p_pow (n : ℕ) : ∥(p : ℤ_[p])^n∥ = p^(-n:ℤ) :=
show ∥((p^n : ℤ_[p]) : ℚ_[p])∥ = p^(-n:ℤ),
by { convert padic.norm_p_pow n, simp, }

def valuation (x : ℤ_[p]) := padic.valuation (x : ℚ_[p])

lemma norm_eq_pow_val {x : ℤ_[p]} (hx : x ≠ 0) :
  ∥x∥ = p^(-x.valuation) :=
begin
  convert padic.norm_eq_pow_val _,
  contrapose! hx,
  exact subtype.val_injective hx
end

@[simp] lemma valuation_zero : valuation (0 : ℤ_[p]) = 0 :=
padic.valuation_zero

@[simp] lemma valuation_one : valuation (1 : ℤ_[p]) = 0 :=
padic.valuation_one

@[simp] lemma valuation_p : valuation (p : ℤ_[p]) = 1 :=
by { delta valuation, exact_mod_cast padic.valuation_p }

lemma valuation_nonneg (x : ℤ_[p]) : 0 ≤ x.valuation :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  have h : (1 : ℝ) < p := by exact_mod_cast nat.prime.one_lt ‹_›,
  rw [← neg_nonpos, ← (fpow_strict_mono h).le_iff_le],
  show ↑p ^ -valuation x ≤ ↑p ^ 0,
  rw [← norm_eq_pow_val hx],
  simpa using x.property,
end

lemma norm_le_pow_iff_norm_lt_pow_succ (x : ℤ_[p]) (n : ℤ) :
  ∥x∥ ≤ p^n ↔ ∥x∥ < p^(n+1) :=
begin
  by_cases hx : x = 0,
  { have hp_pos : (0:ℝ) < p := by exact_mod_cast nat.prime.pos ‹_›,
    have hp_nonneg : (0:ℝ) ≤ p := le_of_lt hp_pos,
    simp [hx, fpow_pos_of_pos hp_pos, fpow_nonneg_of_nonneg hp_nonneg], },
  have hp : (1:ℝ) < p, { exact_mod_cast nat.prime.one_lt ‹_› },
  rw [norm_eq_pow_val hx, (fpow_strict_mono hp).le_iff_le,
    (fpow_strict_mono hp).lt_iff_lt, int.lt_add_one_iff],
end

def mk_units {u : ℚ_[p]} (h : ∥u∥ = 1) : units ℤ_[p] :=
let z : ℤ_[p] := ⟨u, le_of_eq h⟩ in ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]
lemma mk_units_eq {u : ℚ_[p]} (h : ∥u∥ = 1) : ((mk_units h : ℤ_[p]) : ℚ_[p]) = u :=
rfl

lemma exists_repr {x : ℤ_[p]} (hx : x ≠ 0) :
  ∃ (u : units ℤ_[p]) (n : ℕ), x = u*p^n :=
begin
  let u : ℚ_[p] := x*p^(-x.valuation),
  have repr : (x : ℚ_[p]) = u*p^x.valuation,
  { rw [mul_assoc, ← fpow_add],
    { simp },
    { exact_mod_cast nat.prime.ne_zero ‹_› } },
  have hu : ∥u∥ = 1,
    by simp [hx, nat.fpow_ne_zero_of_pos (by exact_mod_cast nat.prime.pos ‹_›) x.valuation,
             norm_eq_pow_val, fpow_neg, inv_mul_cancel],
  obtain ⟨n, hn⟩ : ∃ n : ℕ, valuation x = n,
    from int.eq_coe_of_zero_le (valuation_nonneg x),
  use [mk_units hu, n],
  apply subtype.val_injective,
  simp [hn, repr]
end

variable (p)

lemma span_p_is_maximal :
  (ideal.span ({p} : set ℤ_[p])).is_maximal :=
begin
  rw ideal.is_maximal_iff,
  split,
  { rw ideal.mem_span_singleton', push_neg, intro x,
    assume eq_one,
    suffices : ∥x * p∥ < 1,
    { apply ne_of_lt this, simp [eq_one] },
    have norm_p_lt_one : ∥(p:ℤ_[p])∥ < 1,
    { rw [norm_p], apply inv_lt_one, exact_mod_cast nat.prime.one_lt ‹_›, },
    simpa using mul_lt_mul' x.property norm_p_lt_one (norm_nonneg _) zero_lt_one, },
  { intros I x hI hx_ne hx_mem,
    rw ideal.mem_span_singleton' at hx_ne, push_neg at hx_ne,
    have x_ne_zero : x ≠ 0,
    { specialize hx_ne 0,
      contrapose! hx_ne with x_eq_zero,
      simpa using x_eq_zero.symm, },
    rcases exists_repr x_ne_zero with ⟨u, n, rfl⟩,
    cases n,
    { apply ideal.one_mem_of_unit_mem, simpa using hx_mem, },
    { exfalso,
      apply hx_ne (u*p^n),
      simp [pow_succ', mul_assoc] }, }
end

lemma nonunits_ideal_eq_span :
  nonunits_ideal ℤ_[p] = ideal.span {p} :=
unique_of_exists_unique (max_ideal_unique ℤ_[p])
  (nonunits_ideal.is_maximal _) (span_p_is_maximal p)

lemma nonunits_ideal_fg :
  (nonunits_ideal ℤ_[p]).fg :=
by { rw nonunits_ideal_eq_span, exact ⟨{p}, rfl⟩, }

lemma power_nonunits_ideal_eq_norm_le_pow (n : ℕ) :
  (↑((nonunits_ideal ℤ_[p])^n) : set ℤ_[p]) = {x | ∥x∥ ≤ p^-(n:ℤ) } :=
begin
  rw nonunits_ideal_eq_span p,
  rw ideal.span_singleton_pow,
  ext x,
  erw [ideal.mem_span_singleton', set.mem_set_of_eq],
  split,
  { rintros ⟨y, rfl⟩,
    rw [padic_int.norm_mul, norm_p_pow],
    apply le_of_mul_le_mul_right _ (_ : (p : ℝ)^n > 0),
    rw [mul_assoc, fpow_neg_mul_fpow_self, mul_one],
    { exact y.property },
    { exact_mod_cast ne_of_gt (nat.prime.pos ‹_›) },
    { exact nat.fpow_pos_of_pos (by exact_mod_cast nat.prime.pos ‹_›) (n : ℤ) } },
  { intro h,
    by_cases hx : x = 0, { use 0, simp [hx] },
    { rcases exists_repr hx with ⟨u, n', rfl⟩,
      suffices : n ≤ n',
      { use [u * p^(n' - n)],
        rw [mul_assoc, ← pow_add, nat.sub_add_cancel this], },
      have hp : (1:ℝ) < p, { exact_mod_cast nat.prime.one_lt ‹_› },
      rw [padic_int.norm_mul, is_unit_iff.1 (is_unit_unit u), one_mul, padic_int.norm_pow,
        norm_p, ← fpow_of_nat, ← fpow_inv, ← fpow_mul, (fpow_strict_mono hp).le_iff_le,
        neg_one_mul, neg_le_neg_iff] at h,
      exact_mod_cast h, } },
end

lemma is_adic : is_ideal_adic (nonunits_ideal ℤ_[p]) :=
begin
  rw is_ideal_adic_iff,
  split,
  { intro n,
    show is_open (↑(_ : ideal ℤ_[p]) : set ℤ_[p]),
    rw power_nonunits_ideal_eq_norm_le_pow,
    simp only [norm_le_pow_iff_norm_lt_pow_succ],
    rw ← ball_0_eq,
    exact metric.is_open_ball },
  { intros s hs,
    rcases metric.mem_nhds_iff.mp hs with ⟨ε, ε_pos, hε⟩,
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (p : ℝ)^-(n:ℤ) < ε,
    { have hp : (1:ℝ) < p := by exact_mod_cast nat.prime.one_lt ‹_›,
      obtain ⟨n, hn⟩ : ∃ (n:ℕ), ε⁻¹ < p^n := pow_unbounded_of_one_lt ε⁻¹ hp,
      use n,
      have hp' : (0:ℝ) < p^n,
      { rw ← fpow_of_nat, apply fpow_pos_of_pos, exact_mod_cast nat.prime.pos ‹_› },
      rw [inv_lt ε_pos hp', inv_eq_one_div] at hn,
      rwa [fpow_neg, fpow_of_nat], },
    use n, show (↑(_ : ideal ℤ_[p]) : set ℤ_[p]) ⊆ _,
    refine set.subset.trans _ hε,
    rw power_nonunits_ideal_eq_norm_le_pow,
    rw ball_0_eq,
    intros x hx,
    rw set.mem_set_of_eq at *,
    exact lt_of_le_of_lt hx hn }
end

variable {p}

instance coe_is_ring_hom : is_ring_hom (coe : ℤ_[p] → ℚ_[p]) :=
{ map_one := rfl,
  map_mul := coe_mul,
  map_add := coe_add }

def algebra : algebra ℤ_[p] ℚ_[p] :=
@algebra.of_ring_hom ℤ_[p] _ _ _ (coe) padic_int.coe_is_ring_hom

private lemma aux (p : ℚ) (n : ℤ) (hp : 1 ≤ p) (h : p ^ n < p) : p ^ n ≤ 1 :=
by simpa using fpow_le_of_le hp (le_of_not_lt $ λ h' : 0 < n, not_le_of_lt h $
  by simpa using fpow_le_of_le hp (int.add_one_le_iff.2 h'))

lemma coe_open_embedding : open_embedding (coe : ℤ_[p] → ℚ_[p]) :=
{ induced := rfl, inj := subtype.val_injective, open_range :=
    begin
      show is_open (set.range subtype.val),
      rw subtype.val_range,
      rw show {x : ℚ_[p] | ∥x∥ ≤ 1} = {x : ℚ_[p] | ∥x∥ < p},
      { ext x, split; intro h ; rw set.mem_set_of_eq at h ⊢,
        { calc  ∥x∥ ≤ 1 : h
               ... < _ : by exact_mod_cast (nat.prime.one_lt ‹_›) },
        { by_cases hx : x = 0,
          { simp [hx, zero_le_one] },
          { rcases padic_norm_e.image hx with ⟨n, hn⟩,
            have hp : 1 < p, from nat.prime.one_lt ‹_›,
            rw hn at h ⊢,
            norm_cast at h ⊢,
            apply aux, {exact_mod_cast le_of_lt hp}, {exact h} } } },
      rw ← ball_0_eq,
      exact metric.is_open_ball
    end }

variable (p)

def Huber_ring : Huber_ring ℤ_[p] :=
{ pod := ⟨ℤ_[p], infer_instance, infer_instance, by apply_instance,
  ⟨{ emb := open_embedding_id,
    J := (nonunits_ideal _),
    fin := nonunits_ideal_fg p,
    top := is_adic p,
    .. algebra.id ℤ_[p] }⟩⟩ }

end padic_int

namespace padic
open local_ring padic_int

def Huber_ring : Huber_ring ℚ_[p] :=
{ pod := ⟨ℤ_[p], infer_instance, infer_instance, by apply_instance,
  ⟨{ emb := padic_int.coe_open_embedding,
    J := (nonunits_ideal _),
    fin := nonunits_ideal_fg p,
    top := is_adic p,
    .. padic_int.algebra }⟩⟩ }

end padic
