import data.subtype data.equiv.mul_add ring_theory.ideal_operations
import for_mathlib.data.set.basic
universes u u₁ u₂ v v₁ w

attribute [move_cast] units.inv_eq_inv units.coe_inv
open set

lemma range_units_coe (K : Type*) [division_ring K]: range (coe : units K → K) = -{0} :=
begin
  ext x,
  rw mem_compl_singleton_iff,
  split,
  { rintro ⟨u, hu⟩ h',
    change u.val = x at hu,
    simpa [hu, h'] using u.val_inv },
  { intro h,
    refine ⟨units.mk0 _ h, _⟩,
    change (units.mk0 x h).val = _,
    simp [units.mk0] }
end

lemma range_units_val (K : Type*) [division_ring K]: range (coe : units K → K) = -{0} :=
range_units_coe K

namespace ideal

open function

local attribute [instance] set.pointwise_mul_comm_semiring

-- The following should just be the conjunction of
-- comap f ⊥ = ker f
-- ker f = ⊥  (for injective f)

-- jmc: we have inj_iff_ker_eq_bot in mathlib (ideal_operations.lean). I guess that should work.
-- So I think this one can be deleted.
lemma comap_bot_of_inj {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] (f : R → S) [is_ring_hom f]
(h : injective f) :
  ideal.comap f ⊥ = ⊥ :=
lattice.eq_bot_iff.2 $
begin
  intros r hr,
  change r ∈ f ⁻¹' {0} at hr,
  simp at *,
  apply h,
  rw hr,
  symmetry,
  rw is_ring_hom.map_zero f,
end

end ideal
