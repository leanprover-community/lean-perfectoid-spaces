import data.padics

import for_mathlib.field_power
import for_mathlib.ideal_operations
import for_mathlib.padics

import Huber_pair

/-!
# The p-adics form a Huber ring

In this file we show that ℤ_[p] and ℚ_[p] are Huber rings. They are the fundamental examples
of Huber rings.
-/

noncomputable theory

namespace polynomial

lemma monic.as_sum {R : Type*} [comm_ring R] {f : polynomial R} (hf : f.monic) :
  f = X^(f.nat_degree) + ((finset.range f.nat_degree).sum $ λ i, C (f.coeff i) * X^i) :=
begin
  rw polynomial.ext, intro n,
  rw [coeff_add, coeff_X_pow],
  sorry
  -- split_ifs with h,
  -- { subst h, convert (add_zero _).symm,
  --   { symmetry, exact hf },
  --   { sorry } },
end

end polynomial

open local_ring

local attribute [instance] padic_int.algebra

variables (p : ℕ) [nat.prime p]

namespace padic_int

/-- The topology on ℤ_[p] is adic with respect to the maximal ideal.-/
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

section
open polynomial

lemma is_integrally_closed : is_integrally_closed ℤ_[p] ℚ_[p] :=
{ inj := subtype.val_injective,
  closed :=
  begin
    rintros x ⟨f, f_monic, hf⟩,
    erw subtype.val_range,
    show ∥x∥ ≤ 1,
    by_contra H, push_neg at H,
    rw f_monic.as_sum at hf,
    simp [aeval_def] at hf,
    sorry
  end }

end

/-- The p-adic integers (ℤ_[p])form a Huber ring.-/
instance : Huber_ring ℤ_[p] :=
{ pod := ⟨ℤ_[p], infer_instance, infer_instance, by apply_instance,
  ⟨{ emb := open_embedding_id,
    J := (nonunits_ideal _),
    fin := nonunits_ideal_fg p,
    top := is_adic p,
    .. algebra.id ℤ_[p] }⟩⟩ }

end padic_int

namespace padic
open local_ring

/-- The p-adic numbers (ℚ_[p]) form a Huber ring.-/
instance : Huber_ring ℚ_[p] :=
{ pod := ⟨ℤ_[p], infer_instance, infer_instance, by apply_instance,
  ⟨{ emb := padic_int.coe_open_embedding,
    J := (nonunits_ideal _),
    fin := padic_int.nonunits_ideal_fg p,
    top := padic_int.is_adic p,
    .. padic_int.algebra }⟩⟩ }

def Huber_pair : Huber_pair :=
{ plus := ℤ_[p],
  carrier := ℚ_[p],
  intel :=
  { is_power_bounded :=
    begin
      -- this entire goal ought to follow from some is_bounded.map lemma
      -- but we didn't prove that.
      suffices : is_bounded {x : ℚ_[p] | ∥x∥ ≤ 1},
      { rintro _ ⟨x, rfl⟩,
        show is_power_bounded (x:ℚ_[p]),
        refine is_bounded.subset _ this,
        rintro y ⟨n, rfl⟩,
        show ∥(x:ℚ_[p])^n∥ ≤ 1,
        rw norm_pow,
        exact pow_le_one _ (norm_nonneg _) x.property, },
      have bnd := is_adic.is_bounded ⟨_, (padic_int.is_adic p)⟩,
      intros U hU,
      rcases bnd ((coe : ℤ_[p] → ℚ_[p]) ⁻¹' U) _ with ⟨V, hV, H⟩,
      { use ((coe : ℤ_[p] → ℚ_[p]) '' V),
        sorry, },
      { sorry }
    end
    .. padic_int.coe_open_embedding,
    .. padic_int.is_integrally_closed p } }

end padic
