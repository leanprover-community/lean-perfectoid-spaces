import ring_theory.localization
import tactic.tidy

import nonarchimedean_ring

import for_mathlib.topological_rings
import for_mathlib.algebra
import for_mathlib.top_ring
import for_mathlib.subgroup

universes u v

variables {A  : Type u} [comm_ring A ] [topological_space A ] [topological_ring A ]
variables (T : set A) (s : A)

namespace Huber_ring
open localization algebra topological_ring submodule set

def away (T : set A) (s : A) := away s

namespace away

instance : comm_ring (away T s) := by delta away; apply_instance

instance : module A (away T s) := by delta away; apply_instance

instance : algebra A (away T s) := by delta away; apply_instance

end away

def D : subalgebra A (away T s) :=
let s_inv : (away T s) := ((to_units ⟨s, ⟨1, by simp⟩⟩)⁻¹ : units (away T s)) in
adjoin A {x | ∃ t ∈ T, x = of t * s_inv }

set_option class.instance_max_depth 80

lemma aux₁ (h : nonarchimedean A) (U : open_subgroups A) (a : A) :
  ∃ V : open_subgroups A,
  (span ↥(D T s) (of_id A (away T s) '' V.1)).map
  (lmul_left _ (away T s) ((of_id A (away T s) : A → (away T s)) a))
  ≤ (span ↥(D T s) (of_id A (away T s) '' U.1)) :=
begin
  rcases h _ _ with ⟨V, h₁, h₂, h₃⟩,
  work_on_goal 0 {
    split,
  },
  work_on_goal 0 {
    erw [map_span, span_le, ← image_comp, ← algebra.map_lmul_left, image_comp],
    refine subset.trans (image_subset (of_id A (away T s) : A → (away T s)) _) subset_span, },
  work_on_goal 1 {
    rw image_subset_iff,
    convert h₃, },
    work_on_goal 4 {
      apply mem_nhds_sets,
      { apply continuous_mul_left,
        exact U.2.2 },
      { rw [mem_preimage_eq, linear_map.map_zero],
        apply is_add_submonoid.zero_mem } },
  all_goals { constructor },
  split; assumption
end

instance (h : nonarchimedean A) : topological_space (away T s) :=
topology_of_submodules_comm
(λ U : open_subgroups A, span (D T s) (of_id A (away T s) '' U.1))
begin
  intros U₁ U₂,
  let U₃ : open_subgroups A :=
    ⟨U₁.1 ∩ U₂.1, ⟨is_add_subgroup.inter _ _, is_open_inter U₁.2.2 U₂.2.2⟩⟩,
  use U₃,
  rw lattice.le_inf_iff,
  split;
  rw span_le;
  refine subset.trans (image_subset _ _) subset_span,
  { apply inter_subset_left },
  { apply inter_subset_right },
end
begin
  intros a' U,
  apply localization.induction_on a',
  intros a s',
  let W : open_subgroups A := _,
  cases aux₁ T s h W a with V hV,
  work_on_goal 0 {
    use V,
    erw [localization.mk_eq, mul_comm, lmul_left_mul, map_comp],
    refine le_trans (map_mono hV) _,
    clear hV V, },
end
begin
  intro U,
end

end Huber_ring
