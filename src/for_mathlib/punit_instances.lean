import algebra.punit_instances
import topology.algebra.ring

import for_mathlib.topological_groups

instance : topological_add_monoid unit :=
  { continuous_add := continuous_of_discrete_topology }

instance : topological_ring unit :=
{ continuous_neg := continuous_of_discrete_topology }

open_locale classical

lemma subset_subsingleton {α : Type*} [subsingleton α] (s : set α) :
  s = ∅ ∨ s = set.univ :=
begin
  rw [classical.or_iff_not_imp_left, set.eq_univ_iff_forall],
  intros h x,
  cases set.exists_mem_of_ne_empty h with y hy,
  rwa subsingleton.elim x y
end
