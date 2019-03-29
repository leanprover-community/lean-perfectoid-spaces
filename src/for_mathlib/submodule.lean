import ring_theory.noetherian
import ring_theory.algebra_operations

import for_mathlib.data.set.pointwise_mul

local attribute [instance] classical.prop_decidable

namespace submodule
variables {R : Type*} {M : Type*} [ring R] [add_comm_group M] [module R M]
variables {β : Type*}

lemma sum_mem_span (s : set M) (ι : finset β) (f : β → M) (h : ∀ i ∈ ι, f i ∈ s) :
  ι.sum f ∈ span R s :=
begin
  revert h,
  apply finset.induction_on ι,
  { intros, rw finset.sum_empty, apply submodule.zero_mem _ },
  { intros i ι' hi IH h,
    rw finset.sum_insert hi,
    apply submodule.add_mem _ _ _,
    { apply subset_span,
      apply h,
      apply finset.mem_insert_self },
    { apply IH,
      intros i' hi',
      apply h,
      apply finset.mem_insert_of_mem hi' } }
end

end submodule

namespace submodule
variables {R : Type*} [comm_ring R]
variables (I J : ideal R)

open finset

-- This doesn't work yet, because submodules of an algebra do not yet form a monoid
-- variables {A : Type*} [ring A] [algebra R A]
-- variables (M : submodule R A)

-- lemma fg_pow (h : M.fg) (n : ℕ) : (M^n).fg := _

lemma fg_pow (h : I.fg) (n : ℕ) : (I^n).fg :=
begin
  induction n with n ih,
  { refine ⟨finset.singleton 1, _⟩,
    erw [ideal.span_singleton_eq_top],
    exact is_unit_one },
  { erw pow_succ,
    apply algebra.fg_mul; assumption }
end

end submodule

namespace submodule
open algebra
variables {R : Type*} {A : Type*} [comm_ring R] [ring A] [algebra R A]

local attribute [instance] set.pointwise_mul_semiring

namespace span

-- grrr, we need a mathlib PR to be merged before we can write this.
-- instance : is_semiring_hom (span R : set A → submodule R A) := _

end span

variables (R A)

instance semimodule_set : semimodule (set A) (submodule R A) :=
{ smul := λ s P, span R s * P,
  smul_add := λ _ _ _, mul_add _ _ _,
  add_smul := λ s t P, show span R (s ⊔ t) * P = _, by { erw [span_union, right_distrib] },
  mul_smul := λ s t P, show _ = _ * (_ * _),
    by { rw [← mul_assoc, span_mul_span, set.pointwise_mul_eq_image] },
  one_smul := sorry,
  zero_smul := λ P, show span R ∅ * P = ⊥, by erw [span_empty, bot_mul],
  smul_zero := λ _, mul_bot _ }

variables {R A}

lemma smul_singleton (a : A) (M : submodule R A) :
  ({a} : set A) • M = M.map (lmul_left _ _ a) :=
begin
  conv_lhs {erw ← span_eq M},
  change span _ _ * span _ _ = _,
  erw [span_mul_span, ← set.pointwise_mul_eq_image],
  apply le_antisymm,
  { erw span_le,
    rintros _ ⟨_, h, _, _, rfl⟩,
    erw [mem_map, set.mem_singleton_iff.mp h],
    exact ⟨_, ‹_›, rfl⟩ },
  { rintros _ ⟨_, _, rfl⟩,
    apply subset_span,
    exact ⟨a, set.mem_singleton _, _, ‹_›, rfl⟩ }
end

-- instance mul_action_algebra : mul_action A (submodule R A) :=
-- { smul := λ a M, {a} • M,
--   -- mul_smul := λ s t P, show _ = _ * (_ * _),
--   --   by { rw [← mul_assoc, algebra.span_mul_span, set.pointwise_mul_eq_image] },
--   -- one_smul := sorry }

end submodule
