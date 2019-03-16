import ring_theory.ideal_operations data.equiv.algebra
import for_mathlib.subtype

universes u u₁ u₂ v v₁ w

section

variables {R : Type*} {S : Type*} [monoid R] [monoid S]

lemma mul_left_mul {G : Type*} [semigroup G] (x y : G) :
  (*) (x * y) = (*) x ∘ (*) y :=
funext $ λ _, mul_assoc _ _ _

-- It seems that semigroup homs don't exist in mathlib...
lemma is_monoid_hom.map_mul_left (f : R → S) [is_monoid_hom f] (x : R) :
  f ∘ ((*) x) = ((*) (f x)) ∘ f :=
funext $ λ _, is_monoid_hom.map_mul f

end

namespace submodule

section
variables {R : Type*} [ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {N : Type*} [add_comm_group N] [module R N]
variables (f : M →ₗ[R] N)
variables (s : set M)

lemma map_span : (span R s).map f = span R (f '' s) :=
le_antisymm (map_le_iff_le_comap.2 $ span_le.2 $ λ x hx, subset_span $ set.mem_image_of_mem f hx) $
  span_le.mpr $ set.image_subset _ $ subset_span

end

end submodule

namespace ideal

open function

variables {R : Type*} {S : Type*} [comm_ring R] [comm_ring S]

instance map_is_monoid_hom {f : R → S} [is_ring_hom f] :
  is_monoid_hom (ideal.map f) :=
{ map_one := ideal.map_top f,
  map_mul := ideal.map_mul f }

lemma map_span {R : Type u} [comm_ring R] {S : Type v} [comm_ring S]
  (f : R → S) [is_ring_hom f] (X : set R) :
  map f (span X) = span (f '' X) :=
le_antisymm (map_le_iff_le_comap.2 $ span_le.2 $ λ x hx, subset_span $ set.mem_image_of_mem f hx) $
  span_mono $ set.image_subset _ $ subset_span

@[simp] lemma map_quotient_self {R : Type u} [comm_ring R] (I : ideal R) :
  ideal.map (ideal.quotient.mk I) I = ⊥ :=
lattice.eq_bot_iff.2 $ ideal.map_le_iff_le_comap.2 $
begin
  intros x hx,
  erw submodule.mem_bot I.quotient,
  exact ideal.quotient.eq_zero_iff_mem.2 hx, apply_instance
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
