import ring_theory.algebra_operations
import ring_theory.localization

import tactic.tidy

import for_mathlib.rings

local attribute [instance] set.pointwise_mul_semiring

namespace localization
variables {R : Type*} [comm_ring R] (s : set R) [is_submonoid s]

instance : algebra R (localization R s) :=
algebra.of_ring_hom of (by apply_instance)

end localization
namespace algebra

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

instance : is_monoid_hom (lmul_left R A) :=
{ map_one := linear_map.ext $ λ _, one_mul _,
  map_mul := lmul_left_mul }

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

end

/-

lemma map_eq_comap_symm {M : Type*} {N : Type*}
  [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  (f : M ≃ₗ[R] N) :
  map (↑f : M →ₗ[R] N) = comap ↑f.symm :=
funext $ λ P, ext $ λ x,
begin
  rw [mem_map, mem_comap],
  split; intro h,
  { rcases h with ⟨p, h₁, h₂⟩,
    erw ← f.to_equiv.eq_symm_apply at h₂,
    rwa h₂ at h₁ },
  { exact ⟨_, h, f.apply_symm_apply x⟩ }
end

end
-/
end submodule
