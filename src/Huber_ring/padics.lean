import data.padics
import Huber_ring.basic

variables (p : ℕ) [nat.prime p]

local attribute [-simp] padic.cast_eq_of_rat_of_nat

namespace padic_rat

variable {p}

@[simp] lemma norm_p : ∥(p : ℚ_[p])∥ = p⁻¹ :=
begin
  have p₀ : p ≠ 0 := nat.prime.ne_zero ‹_›,
  have p₁ : p ≠ 1 := nat.prime.ne_one ‹_›,
  simp [p₀, p₁, norm, padic_norm, padic_val_rat, fpow_neg, padic.cast_eq_of_rat_of_nat],
end

@[simp] lemma norm_p_pow (n : ℤ) : ∥(p^n : ℚ_[p])∥ = p^-n :=
by rw [norm_fpow, norm_p, fpow_neg, one_div_eq_inv,
  ← fpow_inv, ← fpow_inv, ← fpow_mul, ← fpow_mul, mul_comm]

end padic_rat

namespace padic_int
open local_ring

variable {p}

@[simp] lemma norm_p : ∥(p : ℤ_[p])∥ = p⁻¹ :=
show ∥((p : ℤ_[p]) : ℚ_[p])∥ = p⁻¹, by exact_mod_cast padic_rat.norm_p

@[simp] lemma norm_p_pow (n : ℕ) : ∥(p : ℤ_[p])^n∥ = p^(-n:ℤ) :=
show ∥((p^n : ℤ_[p]) : ℚ_[p])∥ = p^(-n:ℤ),
by { convert padic_rat.norm_p_pow n, simp, }

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
    sorry }
end

lemma nonunits_ideal_eq_span :
  nonunits_ideal ℤ_[p] = ideal.span {p} :=
unique_of_exists_unique (max_ideal_unique ℤ_[p])
  (nonunits_ideal.is_maximal _) (span_p_is_maximal p)

lemma nonunits_ideal_fg :
  (nonunits_ideal ℤ_[p]).fg :=
by { rw nonunits_ideal_eq_span, exact ⟨{p}, rfl⟩, }

lemma is_adic : is_ideal_adic (nonunits_ideal ℤ_[p]) :=
begin
  rw is_ideal_adic_iff, split,
  { intro n,
    sorry },
  { intros s hs,
    rw mem_nhds_sets_iff at hs,
    rcases hs with ⟨U, hU, x, hx⟩,
    sorry }
end

variable {p}

instance coe_is_ring_hom : is_ring_hom (coe : ℤ_[p] → ℚ_[p]) :=
{ map_one := rfl,
  map_mul := coe_mul,
  map_add := coe_add }

noncomputable def algebra : algebra ℤ_[p] ℚ_[p] :=
@algebra.of_ring_hom ℤ_[p] _ _ _ (coe) padic_int.coe_is_ring_hom

lemma aux (p : ℚ) (n : ℤ) (hp : 1 ≤ p) (h : p ^ n < p) : p ^ n ≤ 1 :=
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

noncomputable def Huber_ring : Huber_ring ℤ_[p] :=
{ pod := ⟨ℤ_[p], infer_instance, infer_instance, by apply_instance,
  ⟨{ emb := open_embedding_id,
    J := (nonunits_ideal _),
    fin := nonunits_ideal_fg p,
    top := is_adic p,
    .. algebra.id ℤ_[p] }⟩⟩ }

end padic_int

namespace padic_rat
open local_ring padic_int

noncomputable def Huber_ring : Huber_ring ℚ_[p] :=
{ pod := ⟨ℤ_[p], infer_instance, infer_instance, by apply_instance,
  ⟨{ emb := padic_int.coe_open_embedding,
    J := (nonunits_ideal _),
    fin := nonunits_ideal_fg p,
    top := is_adic p,
    .. padic_int.algebra }⟩⟩ }

end padic_rat
