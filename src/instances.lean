import data.padics

import Huber_ring

/-
jmc: The first goal of this file is to show that the p-adics form a Huber ring.
jmc: We may extend this with other examples later.
-/

namespace padic_int
open set
variables (p : ℕ) [nat.prime p]

instance coe_is_ring_hom :
  is_ring_hom (λ x, x : ℤ_[p] → ℚ_[p]) :=
by refine {..} ; intros ; simp

def subring : set ℚ_[p] :=
  range (λ x, x : ℤ_[p] → ℚ_[p])

namespace subring

instance is_subring :
  is_subring (subring p) :=
is_ring_hom.is_subring_set_range _

noncomputable def max_ideal : ideal (subring p) :=
ideal.span {(p : subring p)}

def is_open :
  is_open (subring p) :=
begin
  erw [subring, subtype.val_range],
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

end subring

end padic_int

open padic_int

noncomputable instance padic.Huber_ring (p : ℕ) [p.prime] :
  Huber_ring (ℚ_[p]) :=
{ pod := ⟨{
    A₀  := subring p,
    Hr  := by apply_instance,
    Ho  := subring.is_open p,
    J   := subring.max_ideal p,
    fin := ⟨_, infer_instance, rfl⟩,
    top := sorry }⟩ }
