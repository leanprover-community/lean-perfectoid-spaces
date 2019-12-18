import ring_theory.noetherian
import ring_theory.algebra_operations

local attribute [instance] classical.prop_decidable

namespace submodule
open algebra
variables {R : Type*} {A : Type*} [comm_ring R] [comm_ring A] [algebra R A]

local attribute [instance] set.pointwise_mul_semiring
local attribute [instance] set.singleton.is_monoid_hom

set_option class.instance_max_depth 80

lemma smul_eq_smul_span_int (S : set R) (I : ideal R) :
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
      refine ⟨s, hs, a * i, I.mul_mem_left hi, _⟩,
      rw [← mul_assoc, mul_comm s a, mul_assoc, smul_def''],
      refl },
    { rw smul_zero, apply submodule.zero_mem (span _ _) },
    { intros, rw smul_add, apply submodule.add_mem (span _ _), assumption' },
    { intros b si hsi,
      rw [show a • b • si = b • a • si, by {simp}],
      apply submodule.smul_mem (span _ _) b hsi } } }
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

lemma span_span_int (S' : set B) [is_subring S'] (X : set B) : span S' ↑(span ℤ X) = span S' X :=
le_antisymm
begin
  rw span_le,
  intros x hx,
  refine span_induction hx (λ x hx, subset_span hx) (span S' X).zero_mem
    (λ x y hx hy, (span S' X).add_mem hx hy) _,
  intros n b hb,
  erw [smul_def'', ← gsmul_eq_mul],
  apply is_add_subgroup.gsmul_mem hb,
end
(span_mono subset_span)

end

instance mul_action_algebra : mul_action A (submodule R A) :=
{ smul := λ a M, ({a} : set A) • M,
  mul_smul := λ s t P, show ({s * t} : set A) • _ = _,
    by { rw [is_mul_hom.map_mul (singleton : A → set A)], apply mul_smul },
  one_smul := (submodule.semimodule_set R A).one_smul }

end submodule
