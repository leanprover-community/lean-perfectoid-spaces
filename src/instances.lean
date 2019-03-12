import data.padics
import for_mathlib.prime

import Huber_ring

/-
jmc: The first goal of this file is to show that the p-adics form a Huber ring.
jmc: We may extend this with other examples later.
-/

section

open set nat.Prime
variable [nat.Prime]

local attribute [instance] pp

instance padic_int.coe_is_ring_hom :
  is_ring_hom (λ x, x : ℤ_[p] → ℚ_[p]) :=
by refine {..} ; intros ; simp

def padic_int.subring : set ℚ_[p] :=
  range (λ x, x : ℤ_[p] → ℚ_[p])

instance padic_int.subring.is_subring :
  is_subring (padic_int.subring) :=
is_ring_hom.is_subring_set_range _

def padic_int.subring.is_open :
  is_open (padic_int.subring) :=
begin
  erw [padic_int.subring, subtype.val_range],
  convert @metric.is_open_ball _ _ (0 : ℚ_[p]) p,
  funext,
  apply propext,
  suffices : ∥x∥ ≤ 1 ↔ ∥x∥ < p,
  { simpa using this },
  split; intro h,
  { apply lt_of_le_of_lt h,
    convert nat.cast_lt.mpr (nat.prime.gt_one ‹p.prime›),
    rw nat.cast_one, },
  { by_cases H : x = 0,
    { simpa [H] using le_of_lt real.zero_lt_one, },
    cases padic_norm_e.image H with n H,
    rw H at h ⊢,
    -- have := pow_lt_pow_of_lt_left,
    sorry }
end

noncomputable def padic_int.subring.max_ideal : ideal padic_int.subring :=
ideal.span {(nat.cast p : padic_int.subring)}

noncomputable instance padic.Huber_ring : Huber_ring (ℚ_[p]) :=
{ pod := ⟨{
    A₀  := padic_int.subring,
    Hr  := by apply_instance,
    Ho  := padic_int.subring.is_open,
    J   := padic_int.subring.max_ideal,
    fin := ⟨_, infer_instance, rfl⟩,
    top := sorry }⟩ }

end
