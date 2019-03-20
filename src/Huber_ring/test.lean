import ring_theory.localization
import tactic.tidy
import tactic.ring

import nonarchimedean_ring
import Huber_ring.basic

import for_mathlib.topological_rings
import for_mathlib.algebra
import for_mathlib.top_ring
import for_mathlib.subgroup

universes u v

local attribute [instance, priority 0] classical.prop_decidable

namespace Huber_ring
open localization algebra topological_ring submodule set
variables {A  : Type u} [comm_ring A] [topological_space A ] [topological_ring A]
variables (T : set A) (s : A)

def away (T : set A) (s : A) := away s

namespace away

instance : comm_ring (away T s) := by delta away; apply_instance

instance : module A (away T s) := by delta away; apply_instance

instance : algebra A (away T s) := by delta away; apply_instance

def D : subalgebra A (away T s) :=
let s_inv : (away T s) := ((to_units ⟨s, ⟨1, by simp⟩⟩)⁻¹ : units (away T s)) in
adjoin A {x | ∃ t ∈ T, x = of t * s_inv }

set_option class.instance_max_depth 80

lemma directed (U₁ U₂ : open_subgroups A) :
  ∃ (U : open_subgroups A), span ↥(D T s) (⇑(of_id A (away T s)) '' U.val) ≤
    span ↥(D T s) (⇑(of_id A (away T s)) '' U₁.val) ⊓
    span ↥(D T s) (⇑(of_id A (away T s)) '' U₂.val) :=
begin
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

lemma aux₁ (h : nonarchimedean A) (U : open_subgroups A) (a : A) :
  ∃ V : open_subgroups A,
    (span ↥(D T s) (of_id A (away T s) '' V.1)).map
      (lmul_left _ (away T s) ((of_id A (away T s) : A → (away T s)) a)) ≤
    (span ↥(D T s) (of_id A (away T s) '' U.1)) :=
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

lemma mul_subset (h : nonarchimedean A) (U : open_subgroups A) :
∃ (V : open_subgroups A),
    (λ (x : away T s × away T s), x.fst * x.snd) ''
        set.prod ↑(span ↥(D T s) (⇑(of_id A (away T s)) '' V.val))
          ↑(span ↥(D T s) (⇑(of_id A (away T s)) '' V.val)) ≤
      ↑(span ↥(D T s) (⇑(of_id A (away T s)) '' U.val)) :=
begin
  rcases nonarchimedean.mul_subset h U with ⟨V, hV⟩,
  use V,
  refine set.subset.trans _ (span_mono $ image_subset _ hV),
  rw [← image_comp, function.comp],
  simp only [alg_hom.map_mul (of_id _ _)],
  rw image_subset_iff,
  intro x,
  rw set.mem_prod,
  rintros ⟨h₁, h₂⟩,
  rw mem_preimage_eq,
  erw mem_span_iff_lc at h₁ h₂ ⊢,
  rcases h₁ with ⟨lc₁, H₁, hx₁⟩,
  rcases h₂ with ⟨lc₂, H₂, hx₂⟩,
  refine ⟨_, _, _⟩,
  work_on_goal 0 {
    refine lc₁.sum (λ r a, _),
    refine lc₂.sum (λ s b, _),
    exact finsupp.single (r * s) (a * b) },
  work_on_goal 0 {
    rw lc.mem_supported at H₁ H₂ ⊢,
    refine subset.trans finsupp.support_sum _,
    intros a' ha,
    erw finset.mem_bind at ha,
    rcases ha with ⟨a, ha₁, ha₂⟩,
    have hb := finsupp.support_sum ha₂,
    erw finset.mem_bind at hb,
    rcases hb with ⟨b, hb₁, hb₂⟩,
    have H := finsupp.support_single_subset hb₂,
    erw mem_singleton_iff at H,
    subst H,
    replace ha₁ := H₁ ha₁,
    replace hb₁ := H₂ hb₁,
    rw mem_image at ha₁ hb₁ ⊢,
    rcases ha₁ with ⟨a₀, _, _⟩,
    rcases hb₁ with ⟨b₀, _, _⟩,
    use (a₀, b₀),
    split,
    { rw set.mem_prod, split; assumption },
    { simp * } },
  { rw lc.total_apply at hx₁ hx₂ ⊢,
    rw [← hx₁, ← hx₂],
    rw finsupp.sum_mul,
    simp only [finsupp.mul_sum],
    have hyp₁ : ∀ (a : away T s), (0 : away T s) • a = 0 := by intros; simp,
    let hyp₂ : _ := _,
    rw finsupp.sum_sum_index,
    work_on_goal 0 {
      apply finset.sum_congr,
      { refl },
      intros a ha,
      change finsupp.sum _ _ = finsupp.sum _ _,
      erw finsupp.sum_sum_index,
    },
    work_on_goal 2 { exact hyp₂ },
    all_goals { try {exact hyp₁ } },
    work_on_goal 2 {
      intros a b₁ b₂,
      repeat {rw algebra.smul_def},
      rw is_ring_hom.map_add (algebra_map _),
      { rw right_distrib },
      { apply_instance } },
    work_on_goal 1 { assumption },
    work_on_goal 0 {
      clear hyp₁ hyp₂,
      apply finset.sum_congr,
      { refl },
      intros b hb,
      change finsupp.sum _ _ = _,
      rw finsupp.sum_single_index,
      work_on_goal 1 { rw zero_smul },
      dsimp,
      repeat {erw algebra.smul_def},
      rw is_ring_hom.map_mul (algebra_map _),
      { ring },
      all_goals { apply_instance }
    }
  }
end

end away

end Huber_ring

namespace Huber_ring
open localization algebra topological_ring submodule set
variables {A  : Type u} [Huber_ring A]
variables (T : set A) (s : A)

namespace away

/- Wedhorn 6.20 for n = 1-/
lemma mul_T_open (hT : is_open (↑(ideal.span T) : set A)) (U : open_subgroups A) :
  is_open (add_group.closure {x | ∃ t ∈ T, ∃ u ∈ U.val, x = t * u}) :=
begin
  sorry
end

set_option class.instance_max_depth 580

lemma mul_left (hT : is_open (↑(ideal.span T) : set A)) (a : away T s) (U : open_subgroups A) :
  ∃ (V : open_subgroups A),
    map (lmul_left ↥(D T s) (away T s) a) (span ↥(D T s) (⇑(of_id A (away T s)) '' V.val)) ≤
      span ↥(D T s) (⇑(of_id A (away T s)) '' U.val) :=
begin
  apply localization.induction_on a,
  intros a' s',
  clear a,
  suffices : ∃ W : open_subgroups A, _,
  work_on_goal 0 {
    cases this with W hW,
    cases aux₁ T s Huber_ring.nonarchimedean W a' with V hV,
    use V,
    erw [localization.mk_eq, mul_comm, lmul_left_mul, map_comp],
    refine le_trans (map_mono hV) _,
    clear hV V,
    rw lmul_left_units_le_iff,
    rw [inv_inv, to_units_coe],
    exact hW },
  clear a',
  cases s'.property with n hn,
  dsimp,
  change s^n = s' at hn,
  erw ← hn,
  clear hn s',
  induction n with k hk,
  { use U,
    erw [pow_zero, coe_one, lmul_left_one, submodule.map_id],
    exact le_refl _ },
  erw [pow_succ, coe_mul, lmul_left_mul, submodule.map_comp],
  cases hk with W hW,
  suffices : ∃ V : open_subgroups A, _,
  work_on_goal 0 {
    cases this with V hV,
    use V,
    refine le_trans _ (map_mono hW),
    exact hV },
  clear hW U,
  let V : open_subgroups A := ⟨_, by apply_instance, mul_T_open _ hT W⟩,
  use V,
  rw [span_le, image_subset_iff, add_group.closure_subset_iff],
  rintros _ ⟨t, ht, w, hw, rfl⟩,
  rw mem_preimage_eq,
  erw mem_map,
  let s_unit : units (away T s) := to_units ⟨s, ⟨1, by simp⟩⟩,
  let y : away T s := ↑(s_unit⁻¹ : units _) * _,
  work_on_goal 0 {
    use y,
    split,
    work_on_goal 1 {
      rw [lmul_left_apply],
      dsimp only [y],
      erw [← mul_assoc, s_unit.val_inv, one_mul] },
  },
  apply span_mono,
  work_on_goal 1 {
    erw mem_span_singleton,
    work_on_goal 0 {
      let t_over_s : _ := _,
      refine ⟨t_over_s, _⟩,
      work_on_goal 1 {
        dsimp only [y],
        erw [alg_hom.map_mul, ← mul_assoc, smul_def],
        congr' 1,
        rw mul_comm,
      },
      work_on_goal 1 {
        fsplit,
        { exact (of t) * ↑s_unit⁻¹ },
        apply ring.mem_closure,
        apply mem_union_right,
        exact ⟨_, ht, rfl⟩ } } },
  work_on_goal 0 {
    erw singleton_subset_iff,
    use [w, hw] },
  refl
end

instance (hT : is_open (↑(ideal.span T) : set A)) :
  topological_space (away T s) :=
topology_of_submodules_comm
(λ U : open_subgroups A, span (D T s) (of_id A (away T s) '' U.1))
(directed T s) (mul_left T s hT) (mul_subset T s Huber_ring.nonarchimedean)

end away

end Huber_ring
