import ring_theory.ideal_operations data.equiv.algebra

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

namespace ideal

open function

variables {R : Type*} {S : Type*} [comm_ring R] [comm_ring S]

local attribute [instance] set.pointwise_mul_comm_semiring

lemma pow_le_pow (I : ideal R) {m n : ℕ} (h : m ≤ n) :
  I^n ≤ I^m :=
begin
  cases nat.exists_eq_add_of_le h with k hk,
  rw [hk, pow_add],
  exact le_trans (mul_le_inf) (lattice.inf_le_left)
end

lemma mul_subset_mul (I J : ideal R) :
  (↑I : set R) * (↑J : set R) ⊆ (↑(I * J) : set R) :=
begin
  rintros _ ⟨i, hi, j, hj, rfl⟩,
  exact mul_mem_mul hi hj
end

lemma pow_subset_pow (I : ideal R) {n : ℕ} :
  (↑I : set R)^n ⊆ ↑(I^n : ideal R) :=
begin
  induction n with n ih,
  { erw [pow_zero, pow_zero, set.singleton_subset_iff], simp },
  { rw [pow_succ, pow_succ],
    refine set.subset.trans (set.pointwise_mul_subset_mul (set.subset.refl _) ih) _,
    apply mul_subset_mul I (I^n) }
end

-- instance map_is_monoid_hom {f : R → S} [is_ring_hom f] :
--   is_monoid_hom (ideal.map f) :=
-- { map_one := ideal.map_top f,
--   map_mul := ideal.map_mul f }

lemma span_image {R : Type u} [comm_ring R] {S : Type v} [comm_ring S]
  (f : R → S) [is_ring_hom f] (X : set R) :
  span (f '' X) = map f (span X) :=
le_antisymm
  (span_mono $ set.image_subset _ $ subset_span)
  (map_le_iff_le_comap.2 $ span_le.2 $ λ x hx, subset_span $ set.mem_image_of_mem f hx)

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
