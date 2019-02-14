import ring_theory.ideal_operations ring_theory.localization

universes u v

namespace localization
open function

-- This should be moved elsewhere
def r_iff {R : Type u} [comm_ring R] {S : set R} [is_submonoid S] :
  ∀ x y, r R S x y ↔ ∃ t ∈ S, (x.2.1 * y.1 - y.2.1 * x.1) * t = 0
| ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ := iff.rfl

local attribute [instance] classical.prop_decidable

-- This should be moved elsewhere
lemma eq_zero_of {R : Type u} [integral_domain R] (r : R)
(hr : of_comm_ring R (non_zero_divisors R) r = 0) : r = 0 :=
begin
  replace hr := quotient.exact hr,
  dsimp [(≈), setoid.r] at hr,
  erw r_iff at hr,
  rcases hr with ⟨t, ht, ht'⟩,
  replace ht := ne_zero_of_mem_non_zero_divisors ht,
  simpa [ht] using ht'
end

lemma of_comm_ring.injective (R : Type u) [integral_domain R] :
  injective (of_comm_ring R (non_zero_divisors R)) :=
(is_add_group_hom.injective_iff _).mpr eq_zero_of

end localization

namespace ideal
open function

@[simp] lemma map_quotient_self {R : Type u} [comm_ring R] (I : ideal R) :
  ideal.map (ideal.quotient.mk I) I = ⊥ :=
lattice.eq_bot_iff.2 $ ideal.map_le_iff_le_comap.2 $
begin
  intros x hx,
  erw submodule.mem_bot,
  exact ideal.quotient.eq_zero_iff_mem.2 hx
end

lemma eq_bot_or_top {K : Type u} [discrete_field K] (I : ideal K) :
  I = ⊥ ∨ I = ⊤ :=
begin
  rw classical.or_iff_not_imp_right,
  change _ ≠ _ → _,
  rw ideal.ne_top_iff_one,
  intro h1,
  apply le_antisymm, swap, exact lattice.bot_le,
  intros r hr,
  by_cases H : r = 0,
  simpa,
  simpa [H, h1] using submodule.smul_mem I r⁻¹ hr,
end

lemma eq_bot_of_prime {K : Type u} [discrete_field K] (I : ideal K) [h : I.is_prime] :
  I = ⊥ :=
classical.or_iff_not_imp_right.mp I.eq_bot_or_top h.1

-- This should just be the conjunction of
-- comap f ⊥ = ker f
-- ker f = ⊥  (for injective f)
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
