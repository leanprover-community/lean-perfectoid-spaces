-- extending valuations to localizations
-- and extending continuous valuations to rational localizations
-- Note that this file comes much lower down the import tree
-- than stuff like valuation.canonical and valuation.field.
-- Here we use all this Huber ring stuff like R(T/s).

import valuation.field

--local attribute [instance] classical.prop_decidable
--noncomputable theory

universes u u₀

variables {R : Type u₀} [comm_ring R] {S : set R} [is_submonoid S]

namespace valuation
open with_zero

variables {Γ : Type u} [linear_ordered_comm_group Γ]
variables {v : valuation R Γ}

lemma inverse_exists (s : S) : ∃ u : localization R S, u * s = 1 :=
⟨(localization.to_units s).inv, units.inv_val _⟩

-- I realised later on that I could have used the UMP of rings to give
-- a map localization R S -> K_v and then pulled back the canonical valuation.
-- But I was 80% of the way through the proof it was a valuation when I realised this.
def localization_v (h : ∀ s, s ∈ S → v s ≠ 0) : localization R S → with_zero Γ :=
λ (q : localization R S), quotient.lift_on' q (λ rs, v rs.1 * (v rs.2.1)⁻¹)
  begin
    rintros ⟨r1, s1, hs1⟩,
    rintros ⟨r2, s2, hs2⟩,
    intro hrs,
    dsimp [setoid.r, localization.r] at hrs,
    rcases hrs with ⟨t, ht, hrst⟩,
    rw [add_mul, ←neg_mul_eq_neg_mul, add_neg_eq_zero] at hrst,
    show v r1 * (v s1)⁻¹ = v r2 * (v s2)⁻¹,
    apply with_zero.mul_inv_eq_of_eq_mul (h s1 hs1),
    rw [mul_comm, ←mul_assoc],
    apply with_zero.eq_mul_inv_of_mul_eq (h s2 hs2),
    rw [←v.map_mul, ←v.map_mul, mul_comm],
    apply with_zero.mul_right_cancel (h t ht),
    rw [←v.map_mul, ←v.map_mul, hrst]
  end

instance localization_is_valuation (h : ∀ s, s ∈ S → v s ≠ 0) : is_valuation (localization_v h) :=
{ map_zero := show v 0 * (v 1)⁻¹ = 0, by rw [v.map_zero, zero_mul],
  map_one := show v 1 * (v 1)⁻¹ = 1, by {rw [v.map_one], simp},
  map_mul := λ x y, quotient.induction_on₂' x y begin
    rintro ⟨r1, s1, hs1⟩,
    rintro ⟨r2, s2, hs2⟩,
    -- TODO : I had to write the next line "blind" -- I had to be the compiler.
    -- Am I missing a trick?
    show v (r1 * r2) * (v(s1 * s2))⁻¹ = (v r1 * (v s1)⁻¹) * (v r2 * (v s2)⁻¹),
    have hs12 : s1 * s2 ∈ S := is_submonoid.mul_mem hs1 hs2,
    apply with_zero.mul_inv_eq_of_eq_mul (h (s1 * s2) hs12),
    rw [mul_comm _ (v (s1 * s2)), ←mul_assoc, ←mul_assoc],
    apply with_zero.eq_mul_inv_of_mul_eq (h s2 hs2),
    rw [mul_comm _ (v r2), ←v.map_mul, ←mul_assoc, ←v.map_mul, ←mul_assoc, ←v.map_mul],
    apply with_zero.eq_mul_inv_of_mul_eq (h s1 hs1),
    rw [←v.map_mul],
    apply congr_arg, ring,
  end,
  map_add := λ x y, quotient.induction_on₂' x y begin
    rintro ⟨r1, s1, hs1⟩,
    rintro ⟨r2, s2, hs2⟩,
    show v (s1 * r2 + s2 * r1) * (v (s1 * s2))⁻¹ ≤ v r1 * (v s1)⁻¹ ∨
      v (s1 * r2 + s2 * r1) * (v (s1 * s2))⁻¹ ≤ v r2 * (v s2)⁻¹,
    cases v.map_add (r1 * s2) (r2 * s1) with h1 h2,
    { left,
      apply with_zero.le_mul_inv_of_mul_le (h s1 hs1),
      rw [mul_comm, ←mul_assoc],
      apply with_zero.mul_inv_le_of_le_mul (h (s1 * s2) (is_submonoid.mul_mem hs1 hs2)),
      replace h1 := linear_ordered_comm_monoid.mul_le_mul_right h1 (v s1),
      rw [←v.map_mul, ←v.map_mul] at h1 ⊢,
      rw (show s1 * (s1 * r2 + s2 * r1) = (r1 * s2 + r2 * s1) * s1, by ring),
      rwa (show r1 * (s1 * s2) = r1 * s2 * s1, by ring),
    },
    { right,
      apply with_zero.le_mul_inv_of_mul_le (h s2 hs2),
      rw [mul_comm, ←mul_assoc],
      apply with_zero.mul_inv_le_of_le_mul (h (s1 * s2) (is_submonoid.mul_mem hs1 hs2)),
      replace h2 := linear_ordered_comm_monoid.mul_le_mul_right h2 (v s2),
      rw [←v.map_mul, ←v.map_mul] at h2 ⊢,
      rw (show s2 * (s1 * r2 + s2 * r1) = (r1 * s2 + r2 * s1) * s2, by ring),
      rwa (show r2 * (s1 * s2) = r2 * s1 * s2, by ring),
    }
  end }

def localization (h : ∀ s, s ∈ S → v s ≠ 0) : valuation (localization R S) Γ :=
{ val := localization_v h,
  property := by apply_instance }

end valuation
