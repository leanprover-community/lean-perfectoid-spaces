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

set_option class.instance_max_depth 80

lemma smul_eq_smul_spanℤ (S : set R) (I : ideal R) :
  (↑(S • I) : set R) = (↑(S • (span ℤ (↑I : set R))) : set R) :=
begin
  conv_lhs {erw ← span_eq I},
  dsimp only [(•)],
  erw [span_mul_span, span_mul_span],
  apply set.subset.antisymm,
  all_goals {
    intros x hx,
    apply span_induction hx,
    { intros, apply subset_span, assumption },
    { apply submodule.zero_mem (span _ _) },
    { intros, apply submodule.add_mem (span _ _), assumption' },
  { intros a si hsi,
    apply span_induction hsi,
    { rintros _ ⟨s, hs, i, hi, rfl⟩,
      apply subset_span,
      exact ⟨s, hs, a * i, I.mul_mem_left hi, mul_left_comm a s i⟩ },
    { rw smul_zero, apply submodule.zero_mem (span _ _) },
    { intros, rw smul_add, apply submodule.add_mem (span _ _), assumption' },
    { intros b si hsi,
      rw [show a • b • si = b • a • si, from mul_left_comm _ _ _],
      apply submodule.smul_mem (span _ _) b hsi } } }
end

lemma add_group_closure_eq_spanℤ (s : set R) :
  add_group.closure s = ↑(span ℤ s) :=
set.subset.antisymm (add_group.closure_subset subset_span)
  (λ x hx, span_induction hx
  (λ _, add_group.mem_closure)
  (is_add_submonoid.zero_mem _)
  (λ a b ha hb, is_add_submonoid.add_mem ha hb)
  (λ n a ha, by { erw [show n • a = gsmul n a, from (gsmul_eq_mul a n).symm],
    exact is_add_subgroup.gsmul_mem ha}))

@[simp] lemma add_subgroup_eq_spanℤ (s : set R) [is_add_subgroup s] :
  (↑(span ℤ s) : set R) = s :=
begin
  rw ← add_group_closure_eq_spanℤ,
  refine set.subset.antisymm _ add_group.subset_closure,
  rw add_group.closure_subset_iff
end

section
variables {B : Type*} [comm_ring B] [algebra R B]
variables (S : subalgebra R B)

lemma span_mono' (X : set B) : (↑(span R X) : set B) ⊆ span S X :=
λ b hb, span_induction hb
  (λ x hx, subset_span hx)
  (span S X).zero_mem
  (λ x y hx hy, (span S X).add_mem hx hy)
  (λ r b hb, by { rw algebra.smul_def, exact (span S X).smul_mem (algebra_map S r) hb })

lemma span_span' (X : set B) : span S ↑(span R X) = span S X :=
le_antisymm (span_le.mpr $ span_mono' S X) (span_mono subset_span)

lemma span_spanℤ (S' : set B) [is_subring S'] (X : set B) : span S' ↑(span ℤ X) = span S' X :=
le_antisymm
begin
  rw span_le,
  intros x hx,
  refine span_induction hx (λ x hx, subset_span hx) (span S' X).zero_mem
    (λ x y hx hy, (span S' X).add_mem hx hy) _,
  intros n b hb,
  change ↑n * b ∈ _,
  erw ← gsmul_eq_mul,
  apply is_add_subgroup.gsmul_mem hb,
end
(span_mono subset_span)

end

instance mul_action_algebra : mul_action A (submodule R A) :=
{ smul := λ a M, ({a} : set A) • M,
  mul_smul := λ s t P, show ({s * t} : set A) • _ = _,
    by { rw [is_monoid_hom.map_mul (singleton : A → set A)], apply mul_smul },
  one_smul := one_smul _ }

end submodule
