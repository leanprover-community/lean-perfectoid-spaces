import ring_theory.ideal_operations ring_theory.localization data.equiv.algebra
import ring_theory.algebra_operations
import for_mathlib.subtype

universes u u₁ u₂ v

section

variables {R : Type*} {S : Type*} [ring R] [ring S]

lemma mul_left_mul (x y : R) : (*) (x * y) = (*) x ∘ (*) y :=
funext $ λ _, mul_assoc _ _ _

lemma is_ring_hom.map_mul_left (f : R → S) [is_ring_hom f] (x : R) :
  f ∘ ((*) x) = ((*) (f x)) ∘ f :=
funext $ λ _, is_ring_hom.map_mul f

end

namespace localization
variables {R : Type*} [comm_ring R] (s : set R) [is_submonoid s]

instance : algebra R (localization R s) :=
algebra.of_ring_hom of (by apply_instance)

end localization

namespace algebra
open submodule
variables {R : Type*} {A : Type*} [comm_ring R] [comm_ring A] [algebra R A]
variables (M : submodule R A)

lemma mul_left_span_singleton_eq_image (a : A) : ↑(span _ {a} * M) = (*) a '' M :=
begin
  ext x,
  split; intro h,
  { apply algebra.mul_induction_on h,
    { intros a' ha' m hm,
      rw mem_span_singleton at ha',
      cases ha' with r hr,
      use [r • m, M.smul_mem r hm],
      rw [← hr],
      simp },
    { use [0, M.zero_mem],
      exact mul_zero _ },
    { rintros a₁ a₂ ⟨m₁, hm₁, rfl⟩ ⟨m₂, hm₂, rfl⟩,
      use [m₁ + m₂, M.add_mem hm₁ hm₂],
      exact left_distrib _ _ _ },
    { rintros r a' ⟨m, hm, rfl⟩,
      use [r • m, M.smul_mem r hm],
      simp } },
  { rcases h with ⟨m, hm, rfl⟩,
    apply mul_mem_mul _ hm,
    apply subset_span,
    simp }
end

end algebra

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
