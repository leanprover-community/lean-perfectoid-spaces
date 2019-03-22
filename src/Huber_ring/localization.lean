import ring_theory.localization
import tactic.tidy
import tactic.ring

import nonarchimedean_ring
import Huber_ring.basic

import for_mathlib.finset
import for_mathlib.topological_rings
import for_mathlib.algebra
import for_mathlib.lc_algebra
import for_mathlib.top_ring
import for_mathlib.submodule
import for_mathlib.subgroup

universes u v

local attribute [instance, priority 0] classical.prop_decidable

namespace Huber_ring
open localization algebra topological_ring submodule set
variables {A  : Type u} [comm_ring A] [topological_space A ] [topological_ring A]
variables (T : set A) (s : A)

/-
Our goal is to define a topology on (away s), which is the localization of A at s.
This topology will depend on T, and should not depend on the ring of definition.
In the literature, this ring is commonly denoted with A(T/s) to indicate the
dependence on T. For the same reason, we start by defining a wrapper type that
includes T in its assumptions.
-/

/--The localization at `s`, endowed with a topology that depends on `T`-/
def away (T : set A) (s : A) := away s

local notation `ATs` := away T s

namespace away

instance : comm_ring ATs := by delta away; apply_instance

instance : module A ATs := by delta away; apply_instance

instance : algebra A ATs := by delta away; apply_instance

/--An auxiliary subring, used to define the topology on `away T s`-/
def aux : subalgebra A ATs :=
let s_inv : ATs := ((to_units ⟨s, ⟨1, by simp⟩⟩)⁻¹ : units ATs) in
adjoin A {x | ∃ t ∈ T, x = of t * s_inv }

local notation `D` := aux T s

/-
To put a topology on `away T s` we want to use the construction
`topology_of_submodules_comm` which needs a directed family of
submodules of `ATs = away T s` viewed as `D`-algebra.
This directed family has two satisfy two extra conditions.
Proving these two conditions takes up the beef of this file.

Initially we only assume that `A` is a nonarchimedean ring,
but towards the end we need to strengthen this assumption to Huber ring.
-/

set_option class.instance_max_depth 80

/-The submodules spanned by the open subgroups of `A` form a directed family-/
lemma directed (U₁ U₂ : open_add_subgroups A) :
  ∃ (U : open_add_subgroups A), span ↥D (⇑(of_id A ATs) '' U.val) ≤
    span ↥D (⇑(of_id A ATs) '' U₁.val) ⊓ span ↥D (⇑(of_id A ATs) '' U₂.val) :=
begin
  let U₃ : open_add_subgroups A :=
    ⟨U₁.1 ∩ U₂.1, ⟨is_add_subgroup.inter _ _, is_open_inter U₁.2.2 U₂.2.2⟩⟩,
  use U₃,
  rw lattice.le_inf_iff,
  split;
  rw span_le;
  refine subset.trans (image_subset _ _) subset_span,
  { apply inter_subset_left },
  { apply inter_subset_right },
end

/-For every open subgroup `U` of `A` and every `a : A`,
there exists an open subgroup `V` of `A`,
such that `a . (span D V)` is contained in the `D`-span of `U`.-/
lemma exists_mul_left_subset (h : nonarchimedean A) (U : open_add_subgroups A) (a : A) :
  ∃ V : open_add_subgroups A,
    (span ↥D (of_id A ATs '' V.1)).map (lmul_left _ ATs ((of_id A ATs : A → ATs) a)) ≤
    (span ↥D (of_id A ATs '' U.1)) :=
begin
  rcases h _ _ with ⟨V, h₁, h₂, h₃⟩,
  let W : open_add_subgroups A := ⟨V, h₁, h₂⟩,
  use W,
  work_on_goal 0 {
    erw [← span_image, span_le, ← image_comp, ← algebra.map_lmul_left, image_comp],
    refine subset.trans (image_subset (of_id A ATs : A → ATs) _) subset_span,
    rw image_subset_iff,
    exact h₃ },
  apply mem_nhds_sets (continuous_mul_left _ _ U.2.2),
  { rw [mem_preimage_eq, mul_zero],
    apply is_add_submonoid.zero_mem }
end

/-For every open subgroup `U` of `A`, there exists an open subgroup `V` of `A`,
such that the multiplication map sends the `D`-span of `V` into the `D`-span of `U`.-/
lemma mul_subset (h : nonarchimedean A) (U : open_add_subgroups A) :
∃ (V : open_add_subgroups A),
    (λ (x : away T s × away T s), x.fst * x.snd) ''
        set.prod ↑(span ↥D (⇑(of_id A ATs) '' V.val))
          ↑(span ↥D (⇑(of_id A ATs) '' V.val)) ≤
      ↑(span ↥D (⇑(of_id A ATs) '' U.val)) :=
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
  refine ⟨lc₁ * lc₂, _, _⟩,
  work_on_goal 0 {
    rw lc.mem_supported at H₁ H₂ ⊢,
    refine subset.trans (lc.support_mul _ _) _,
    intros a' ha,
    erw finset.mem_image at ha,
    rcases ha with ⟨y, hy₁, hy₂⟩,
    rw finset.mem_product at hy₁,
    rw ← hy₂,
    have ha₁ := H₁ hy₁.left,
    have hb₁ := H₂ hy₁.right,
    rw mem_image at ha₁ hb₁ ⊢,
    rcases ha₁ with ⟨a₀, _, _⟩,
    rcases hb₁ with ⟨b₀, _, _⟩,
    use (a₀, b₀),
    split,
    { rw set.mem_prod, split; assumption },
    { simp * } },
  { rw [← hx₁, ← hx₂],
    exact lc.atotal.map_mul _ _ }
end

lemma K.aux (L : finset A) (h : (↑L : set A) ⊆ ideal.span T) :
  ∃ (K : finset A),
  (↑L : set A) ⊆ add_group.closure {x | ∃ (t ∈ T) (k ∈ (↑K : set A)), x = t * k} :=
begin
  delta ideal.span at h,
  erw span_eq_map_lc at h,
  choose s hs using finset.exists_finset_of_subset_image L _ _ h,
  use s.bind (λ f, f.frange),
  intros l hl,
  cases hs with h' hs,
  subst h',
  erw finset.mem_image at hl,
  rcases hl with ⟨f, hf, rfl⟩,
  apply add_group.mclosure_subset,
  apply add_monoid.sum_mem_closure,
  intros t ht,
  refine ⟨t, _, _, _, mul_comm _ _⟩,
  { replace hf := hs hf,
    erw lc.mem_supported at hf,
    exact hf ht },
  { erw [linear_map.id_apply, finset.mem_bind],
    use [f, hf],
    erw finsupp.mem_support_iff at ht,
    erw finsupp.mem_frange,
    exact ⟨ht, ⟨t, rfl⟩⟩ }
end

end away

end Huber_ring

namespace Huber_ring
open localization algebra topological_ring submodule set
variables {A  : Type u} [Huber_ring A]
variables (T : set A) (s : A)

namespace away

local notation `ATs` := away T s
local notation `D` := aux T s

/- Wedhorn 6.20 for n = 1-/
lemma mul_T_open (hT : is_open (↑(ideal.span T) : set A)) (U : open_add_subgroups A) :
  is_open (add_group.closure {x | ∃ t ∈ T, ∃ u ∈ U.val, x = t * u}) :=
begin
  -- we need to remember that A is nonarchimedean, before we destruct the Huber ring instance
  have nonarch : nonarchimedean A := Huber_ring.nonarchimedean,
  tactic.unfreeze_local_instances,
  rcases ‹Huber_ring A› with ⟨_, _, _, ⟨A₀, _, _, _, ⟨_, emb, hf, I, fg, top⟩⟩⟩,
  resetI,
  rcases (is_ideal_adic_iff I).mp top with ⟨H₁, H₂⟩,
  cases H₂ _ (mem_nhds_sets (emb.continuous _ hT) _) with n hn,
  work_on_goal 1 {
    rw mem_preimage_eq,
    erw is_ring_hom.map_zero (to_fun A),
    { exact (ideal.span _).zero_mem },
    apply_instance },
  cases fg_pow I fg n with L hL,
  rw ← hL at hn,
  have Lsub := set.subset.trans subset_span hn,
  rw ← image_subset_iff at Lsub,
  rw ← finset.coe_image at Lsub,
  cases K.aux _ _ Lsub with K hK,
  let V := K.inf (λ a : A, classical.some (nonarch.left_mul_subset U a)),
  cases H₂ _ (mem_nhds_sets (emb.continuous _ V.2.2) _) with m hm,
  work_on_goal 1 {
    rw mem_preimage_eq,
    erw is_ring_hom.map_zero (to_fun A),
    { exact is_add_submonoid.zero_mem _ },
    apply_instance },
  rw ← image_subset_iff at hm,
  apply @open_add_subgroups.is_open_of_open_add_subgroup A _ _ _ _
    (add_group.closure.is_add_subgroup _),
  refine ⟨⟨to_fun A '' ↑(I^(m+1)), _, _⟩, _⟩,
  work_on_goal 2 { assumption },
  all_goals { try {apply_instance} },
  { exact embedding_open emb hf (H₁ _) },
  have hIm :
    (add_group.closure {x | ∃ t ∈ T, ∃ ki ∈
      add_group.closure {ki | ∃ k ∈ K, ∃ i ∈ ((to_fun A : A₀ → A) '' ↑(I^m)), ki = k * i},
        x = t * ki}) ⊆ _ := _,
  work_on_goal 0 { refine set.subset.trans _ hIm, clear hIm },
  work_on_goal 1 {
    apply add_group.closure_mono,
    rintros _ ⟨t, ht, ki, hki, rfl⟩,
    use [t, ht],
    refine ⟨_, _, rfl⟩,
    apply add_group.in_closure.rec_on hki,
    { rintros _ ⟨k, hk, i, hi, rfl⟩,
      replace hi := hm hi,
      have H : V ≤ classical.some (nonarch.left_mul_subset U k) := finset.inf_le hk,
      replace hi := H hi,
      apply classical.some_spec (nonarch.left_mul_subset U k),
      use [i, hi] },
    { apply is_add_submonoid.zero_mem },
    { intros, apply is_add_subgroup.neg_mem, assumption },
    { intros, apply is_add_submonoid.add_mem; assumption } },
  all_goals {sorry}
end

set_option class.instance_max_depth 150

lemma mul_left (hT : is_open (↑(ideal.span T) : set A)) (a : away T s) (U : open_add_subgroups A) :
  ∃ (V : open_add_subgroups A),
    map (lmul_left ↥D ATs a) (span ↥D (⇑(of_id A ATs) '' V.val)) ≤
      span ↥D (⇑(of_id A ATs) '' U.val) :=
begin
  apply localization.induction_on a,
  intros a' s',
  clear a,
  suffices : ∃ W : open_add_subgroups A, _,
  work_on_goal 0 {
    cases this with W hW,
    cases exists_mul_left_subset T s Huber_ring.nonarchimedean W a' with V hV,
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
  suffices : ∃ V : open_add_subgroups A, _,
  work_on_goal 0 {
    cases this with V hV,
    use V,
    refine le_trans _ (map_mono hW),
    exact hV },
  clear hW U,
  let V : open_add_subgroups A := ⟨_, by apply_instance, mul_T_open _ hT W⟩,
  use V,
  rw [span_le, image_subset_iff, add_group.closure_subset_iff],
  rintros _ ⟨t, ht, w, hw, rfl⟩,
  rw mem_preimage_eq,
  erw mem_map,
  let s_unit : units ATs := to_units ⟨s, ⟨1, by simp⟩⟩,
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
  topological_space ATs :=
topology_of_submodules_comm
(λ U : open_add_subgroups A, span D (of_id A ATs '' U.1))
(directed T s) (mul_left T s hT) (mul_subset T s Huber_ring.nonarchimedean)

end away

end Huber_ring
