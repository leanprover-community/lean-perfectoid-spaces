import ring_theory.algebra_operations
import ring_theory.localization

import for_mathlib.rings
import for_mathlib.top_ring

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

section
variables {R : Type*} [comm_ring R]
variables {A : Type*} [ring A] [algebra R A]
variables {B : Type*} [ring B] [algebra R B]
variables (f : A →ₐ[R] B)

lemma map_lmul_left (a : A) :
  f ∘ (lmul_left R A a) = (lmul_left R B (f a)) ∘ f :=
funext $ λ b, f.map_mul a b

lemma lmul_left_mul (a b : A) :
  lmul_left R A (a * b) = (lmul_left R A a).comp (lmul_left R A b) :=
linear_map.ext $ λ _, mul_assoc _ _ _

end

end algebra

namespace submodule
open algebra

variables {R : Type*} [comm_ring R]

section
variables {A : Type*} [ring A] [algebra R A]
variables {B : Type*} [ring B] [algebra R B]
variables (f : A →ₐ[R] B)
variables (M N : submodule R A)

attribute [simp] comap_id

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

@[simp] lemma lmul_left_one : lmul_left R A 1 = linear_map.id :=
linear_map.ext $ λ _, one_mul _

lemma lmul_left_comp (a : A) :
  f.to_linear_map.comp (lmul_left R A a) = (lmul_left R B (f a)).comp f.to_linear_map :=
linear_map.ext $ λ b, f.map_mul a b

lemma map_lmul_left_inv (a : units A) :
  map (lmul_left R A ↑a⁻¹) = comap (lmul_left R A a) :=
funext $ λ M, ext $ λ m, by { rw mem_map, }
-- le_antisymm
--   (by { rw [map_le_iff_le_comap, ← comap_comp, ← lmul_left_mul], simp [le_refl] })
--   (by {  })

lemma lmul_left_units_le_iff (a : units A) :
  M.map (lmul_left _ _ a) ≤ N ↔ M ≤ N.map (lmul_left _ _ ↑a⁻¹) :=
by rw [map_le_iff_le_comap, map_lmul_left_inv]

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

section comm_algebra
open algebra

variables {R : Type*} {A: Type*} [comm_ring R] [comm_ring A] [algebra R A]
  {ι : Type*} [inhabited ι] (M : ι → submodule R A)
  (h_directed : ∀ i j, ∃ k, M k ≤ M i ⊓ M j)
  (h_left_mul : ∀ x i, ∃ j, (M j).map (lmul_left _ _ x) ≤ M i)
  (h_mul : ∀ i, ∃ j, (λ x : A × A, x.1*x.2) '' (set.prod (M j) (M j)) ≤ M i)
include h_directed h_left_mul h_mul

def of_submodules_comm : ring_with_zero_nhd A :=
of_subgroups_comm (λ i, (M i : set A)) h_directed h_left_mul h_mul

def topology_of_submodules_comm : topological_space A :=
topology_of_subgroups_comm (λ i, (M i : set A)) h_directed h_left_mul h_mul

lemma of_submodules_comm.nhds_zero (U : set A) :
  U ∈ @nhds A (topology_of_submodules_comm _ h_directed h_left_mul h_mul)
    (0 : A) ↔ ∃ i, (M i : set A) ⊆ U :=
of_subgroups.nhds_zero _ _ _ _ _ _

end comm_algebra
