import ring_theory.noetherian
import ring_theory.algebra_operations

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
    erw [pow_zero, ideal.one_eq_top, ideal.span_singleton_eq_top],
    exact is_unit_one },
  { erw pow_succ,
    apply fg_mul; assumption }
end

end submodule

namespace submodule
open algebra
variables {R : Type*} {A : Type*} [comm_ring R] [ring A] [algebra R A]

local attribute [instance] set.pointwise_mul_semiring
local attribute [instance] set.singleton.is_monoid_hom

instance span.is_semiring_hom : is_semiring_hom (submodule.span R : set A → submodule R A) :=
{ map_zero := span_empty,
  map_one := show _ = map _ ⊤,
    by erw [← ideal.span_singleton_one, ← span_image, set.image_singleton, alg_hom.map_one]; refl,
  map_add := span_union,
  map_mul := λ s t, by erw [span_mul_span, set.pointwise_mul_eq_image] }

variables (R A)

instance semimodule_set : semimodule (set A) (submodule R A) :=
{ smul := λ s P, span R s * P,
  smul_add := λ _ _ _, mul_add _ _ _,
  add_smul := λ s t P, show span R (s ⊔ t) * P = _, by { erw [span_union, right_distrib] },
  mul_smul := λ s t P, show _ = _ * (_ * _),
    by { rw [← mul_assoc, span_mul_span, set.pointwise_mul_eq_image] },
  one_smul := λ P, show span R {(1 : A)} * P = _,
    by { conv_lhs {erw ← span_eq P}, erw [span_mul_span, one_mul, span_eq] },
  zero_smul := λ P, show span R ∅ * P = ⊥, by erw [span_empty, bot_mul],
  smul_zero := λ _, mul_bot _ }

variables {R A}

set_option class.instance_max_depth 40

lemma smul_def {s : set A} {P : submodule R A} :
  s • P = span R s * P := rfl

lemma smul_le_smul {s t : set A} {M N : submodule R A} (h₁ : s ≤ t) (h₂ : M ≤ N) :
  s • M ≤ t • N :=
mul_le_mul (span_mono h₁) h₂

lemma smul_singleton (a : A) (M : submodule R A) :
  ({a} : set A) • M = M.map (lmul_left _ _ a) :=
begin
  conv_lhs {erw ← span_eq M},
  change span _ _ * span _ _ = _,
  erw [span_mul_span],
  apply le_antisymm,
  { erw span_le,
    rintros _ ⟨_, h, _, _, rfl⟩,
    erw [mem_map, set.mem_singleton_iff.mp h],
    exact ⟨_, ‹_›, rfl⟩ },
  { rintros _ ⟨_, _, rfl⟩,
    apply subset_span,
    exact ⟨a, set.mem_singleton _, _, ‹_›, rfl⟩ }
end

instance mul_action_algebra : mul_action A (submodule R A) :=
{ smul := λ a M, ({a} : set A) • M,
  mul_smul := λ s t P, show ({s * t} : set A) • _ = _,
    by { rw [is_monoid_hom.map_mul (singleton : A → set A)], apply mul_smul },
  one_smul := one_smul _ }

end submodule
