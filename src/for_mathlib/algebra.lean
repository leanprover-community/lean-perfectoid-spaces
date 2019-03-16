import ring_theory.algebra_operations
import ring_theory.localization

import for_mathlib.rings

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
variables {R : Type*} {A : Type*} {B : Type*} {C : Type*}
variables [comm_ring R] [ring A] [ring B] [ring C]
variables [algebra R A] [algebra R B] [algebra R C]

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

/-
TODO(jmc):
* Introduce submodule.principal (R) (m : M) : submodule R M for every module R M.
* (Maybe show some results for the special case ideal.principal.)
* Prove that submodule R A is a (comm) ring. We currently only have (comm) semigroup.
* Show that principal R : A → submodule R A is a monoid hom.
-/

-- TODO(jmc): Uncommenting these lines breaks things down the file.
-- I have not yet investigated.

-- def one : submodule R A :=
-- submodule.map (of_id R A).to_linear_map (1 : ideal R)

-- instance : monoid (submodule R A) :=
-- { one := one,
--   one_mul :=
--   begin
--     intro M,
--     apply le_antisymm,
--     { rw mul_le,
--       sorry },
--     { sorry }
--   end,
--   mul_one := sorry,
--   ..algebra.semigroup }

-- TODO: comm_monoid if A is comm_ring

end

end submodule
