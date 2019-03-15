import ring_theory.ideal_operations ring_theory.localization data.equiv.algebra
import ring_theory.algebra_operations
import for_mathlib.subtype

universes u u₁ u₂ v v₁ w

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

section span_mul
open submodule
variables {R : Type*} {A : Type*} [comm_ring R] [ring A] [algebra R A]
variables (M : submodule R A)

lemma mul_left_span_singleton_eq_image (a : A) :
  span R {a} * M = map (lmul_left R A a) M :=
begin
  apply le_antisymm,
  { rw mul_le,
    intros a' ha' m hm,
    rw mem_span_singleton at ha',
    rcases ha' with ⟨r, rfl⟩,
    use [r • m, M.smul_mem r hm],
    simp },
  { rintros _ ⟨m, hm, rfl⟩,
    apply mul_mem_mul _ hm,
    apply subset_span,
    simp }
end

lemma mul_left_span_singleton_eq_image' (a : A) : ↑(span _ {a} * M) = (*) a '' M :=
congr_arg submodule.carrier (mul_left_span_singleton_eq_image M a)

end span_mul

section to_linear_map
variables {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}
variables [comm_ring R] [ring A] [ring B] [ring C] [ring D]
variables [algebra R A] [algebra R B] [algebra R C] [algebra R D]

@[simp] lemma to_linear_map_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  (g.comp f).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

end to_linear_map

end algebra

namespace submodule
open algebra

variables {R : Type*} [comm_ring R]

section
variables {A : Type*} [ring A] [algebra R A]
variables {B : Type*} [ring B] [algebra R B]
variables (f : A →ₐ[R] B)
variables (M N : submodule R A)

lemma map_mul : (M * N).map f.to_linear_map = M.map f.to_linear_map * N.map f.to_linear_map :=
begin
  apply le_antisymm,
  { rw [map_le_iff_le_comap, mul_le],
    intros,
    erw [mem_comap, f.map_mul],
    apply mul_mem_mul; refine ⟨_, ‹_›, rfl⟩ },
  { rw mul_le,
    rintros _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩,
    use [m * n, mul_mem_mul hm hn],
    apply f.map_mul }
end

lemma map_lmul_left (a : A) :
  f.to_linear_map.comp (lmul_left R A a) = (lmul_left R B (f a)).comp f.to_linear_map :=
linear_map.ext $ λ b, f.map_mul a b

def one : submodule R A :=
submodule.map (of_id R A).to_linear_map (1 : ideal R)

instance : monoid (submodule R A) :=
{ one := one,
  one_mul :=
  begin
    intro M,
    apply le_antisymm,
    { rw mul_le,
      sorry },
    { sorry }
  end,
  mul_one := sorry,
  ..algebra.semigroup }

-- TODO: comm_monoid if A is comm_ring

end

section
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
