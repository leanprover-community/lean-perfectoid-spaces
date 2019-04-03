import ring_theory.localization
import tactic.tidy
import tactic.ring

import Huber_ring.basic

import for_mathlib.finset
import for_mathlib.topological_rings
import for_mathlib.algebra
import for_mathlib.submodule
import for_mathlib.subgroup
import for_mathlib.nonarchimedean.basic

universes u v

local attribute [instance, priority 0] classical.prop_decidable

local attribute [instance] set.pointwise_mul_semiring

namespace Huber_ring
open localization algebra topological_ring submodule set topological_add_group
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
adjoin A (s_inv • of_id A ATs '' T)

local notation `D` := aux T s

local notation `Dspan` U := span D (of_id A ATs '' U)

/-
To put a topology on `away T s` we want to use the construction
`topology_of_submodules_comm` which needs a directed family of
submodules of `ATs = away T s` viewed as `D`-algebra.
This directed family has two satisfy two extra conditions.
Proving these two conditions takes up the beef of this file.

Initially we only assume that `A` is a nonarchimedean ring,
but towards the end we need to strengthen this assumption to Huber ring.
-/

set_option class.instance_max_depth 50

/-The submodules spanned by the open subgroups of `A` form a directed family-/
lemma directed (U₁ U₂ : open_add_subgroup A) :
  ∃ (U : open_add_subgroup A), span ↥D (⇑(of_id A ATs) '' U.val) ≤
    span ↥D (⇑(of_id A ATs) '' U₁.val) ⊓ span ↥D (⇑(of_id A ATs) '' U₂.val) :=
begin
  use U₁ ⊓ U₂,
  apply lattice.le_inf _ _;
    rw span_le;
    refine subset.trans (image_subset _ _) subset_span,
  { apply inter_subset_left },
  { apply inter_subset_right },
end

/-For every open subgroup `U` of `A` and every `a : A`,
there exists an open subgroup `V` of `A`,
such that `a • (span D V)` is contained in the `D`-span of `U`.-/
lemma exists_mul_left_subset (h : nonarchimedean A) (U : open_add_subgroup A) (a : A) :
  ∃ V : open_add_subgroup A, ((of_id A ATs : A → ATs) a) • (Dspan V) ≤ (Dspan U) :=
begin
  cases h _ _ with V hV,
  use V,
  work_on_goal 0 {
    erw [smul_singleton, ← span_image, span_le, ← image_comp, ← algebra.map_lmul_left, image_comp],
    refine subset.trans (image_subset (of_id A ATs : A → ATs) _) subset_span,
    rw image_subset_iff,
    exact hV },
  apply mem_nhds_sets (continuous_mul_left _ _ U.is_open),
  { rw [mem_preimage_eq, mul_zero],
    apply is_add_submonoid.zero_mem }
end

/-For every open subgroup `U` of `A`, there exists an open subgroup `V` of `A`,
such that the multiplication map sends the `D`-span of `V` into the `D`-span of `U`.-/
lemma mul_le (h : nonarchimedean A) (U : open_add_subgroup A) :
  ∃ (V : open_add_subgroup A), (Dspan V) * (Dspan V) ≤ (Dspan U) :=
begin
  rcases nonarchimedean.mul_subset h U with ⟨V, hV⟩,
  use V,
  rw span_mul_span,
  apply span_mono,
  rw ← is_semiring_hom.map_mul (image (of_id A ATs : A → ATs)),
  exact image_subset _ hV,
end

lemma K.aux (L : finset A) (h : (↑L : set A) ⊆ ideal.span T) :
  ∃ (K : finset A), (↑L : set A) ⊆ (↑(span ℤ (T * ↑K)) : set A) :=
begin
  delta ideal.span at h,
  erw span_eq_map_lc at h,
  choose s hs using finset.exists_finset_of_subset_image L _ _ h,
  use s.bind (λ f, f.frange),
  rcases hs with ⟨rfl, hs⟩,
  intros l hl,
  rcases finset.mem_image.mp hl with ⟨f, hf, rfl⟩,
  apply submodule.sum_mem_span,
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
open localization algebra topological_ring submodule set topological_add_group
variables {A  : Type u} [Huber_ring A]
variables (T : set A) (s : A)

namespace away

local notation `ATs` := away T s
local notation `D` := aux T s
local notation `Dspan` U := span D (of_id A ATs '' U)

set_option class.instance_max_depth 150

/- Wedhorn 6.20 for n = 1-/
lemma mul_T_open (hT : is_open (↑(ideal.span T) : set A)) (U : open_add_subgroup A) :
  is_open (↑(T • span ℤ (U : set A)) : set A) :=
begin
  -- Choose an ideal I ⊆ span T
  rcases exists_pod_subset _ (mem_nhds_sets hT $ ideal.zero_mem $ ideal.span T)
    with ⟨A₀, _, _, _, ⟨_, emb, hf, I, fg, top⟩, hI⟩,
  resetI, dsimp only at hI,
  -- Choose a generating set L ⊆ I
  cases fg with L hL,
  rw ← hL at hI,
  have Lsub := set.subset.trans (image_subset _ _) hI,
  work_on_goal 2 { apply subset_span },
  rw [← finset.coe_image] at Lsub,
  -- Choose a finite set K such that L ⊆ span (T * K)
  cases K.aux _ _ Lsub with K hK,
  -- Choose V such that K * V ⊆ U
  let V := K.inf (λ k : A, classical.some (Huber_ring.nonarchimedean.left_mul_subset U k)),
  cases (is_ideal_adic_iff I).mp top with H₁ H₂,
  -- Choose m such that I^m ⊆ V
  cases H₂ _ (mem_nhds_sets (emb.continuous _ V.is_open) _) with m hm,
  work_on_goal 1 {
    erw [mem_preimage_eq, is_ring_hom.map_zero (to_fun A)],
    { exact V.zero_mem },
    apply_instance },
  rw ← image_subset_iff at hm,
  -- It suffices to provide an open subgroup
  apply @open_add_subgroup.is_open_of_open_add_subgroup A _ _ _ _
    (submodule.submodule_is_add_subgroup _),
  refine ⟨⟨to_fun A '' ↑(I^(m+1)), _, _⟩, _⟩,
  work_on_goal 2 {assumption},
  all_goals { try {apply_instance} },
  { exact embedding_open emb hf (H₁ _) },
  rw subtype.coe_mk,
  calc _ = (to_fun A : A₀ → A) '' ↑(I^(m+1)) : rfl
     ... ⊆ to_fun A '' ↑(↑L • I^m : submodule A₀ A₀) : by rw [pow_succ, ← hL, submodule.smul_def]
    --  ... = to_fun A '' ↑(span A₀ ↑L) * to_fun A '' ↑(I^m) :
    --         by { apply is_monoid_hom.map_mul (image (to_fun A : A₀ → A)), }
     ... ⊆ _ : sorry,
  all_goals {sorry}
--  rw [pow_add, pow_one, ← hL],
--  have hIm :
--    (add_group.closure {x | ∃ t ∈ T, ∃ ki ∈
--      add_group.closure {ki | ∃ k ∈ K, ∃ i ∈ ((to_fun A : A₀ → A) '' ↑(I^m)), ki = k * i},
--        x = t * ki}) ⊆ _ := _,
--  work_on_goal 0 { refine set.subset.trans _ hIm, clear hIm },
--  work_on_goal 1 {
--    apply add_group.closure_mono,
--    rintros _ ⟨t, ht, ki, hki, rfl⟩,
--    use [t, ht],
--    refine ⟨_, _, rfl⟩,
--    apply add_group.in_closure.rec_on hki,
--    { rintros _ ⟨k, hk, i, hi, rfl⟩,
--      replace hi := hm hi,
--      have H : V ≤ classical.some (nonarch.left_mul_subset U k) := finset.inf_le hk,
--      replace hi := H hi,
--      apply classical.some_spec (nonarch.left_mul_subset U k),
--      use [i, hi] },
--    { apply is_add_submonoid.zero_mem },
--    { intros, apply is_add_subgroup.neg_mem, assumption },
--    { intros, apply is_add_submonoid.add_mem; assumption } },
--  { have := set.prod_mono hK (set.subset.refl (to_fun A '' ↑(I^m))),
--    replace := set.image_subset (λ x : A × A, x.1 * x.2) this,
--    replace := add_group.closure_mono this,
--    convert this using 1,
--    { clear this,
--      change to_fun A '' _ = _,
--      erw [pow_add, ← hL, finset.coe_image, set.prod_image_image_eq, ← image_comp],
--      change _ = add_group.closure ((λ (x : A₀ × A₀), (to_fun A (x.fst) * to_fun A (x.snd))) ''
--          set.prod ↑L ↑(I^m)),
--      haveI : is_ring_hom (to_fun A : A₀ → A) := by apply_instance,
--      conv_rhs { congr, congr, funext, rw ← is_ring_hom.map_mul (to_fun A : A₀ → A) },
--      change _ = add_group.closure ((to_fun A ∘ (λ (x : A₀ × A₀), x.fst * x.snd)) ''
--          set.prod ↑L ↑(I^m)),
--      conv_rhs {rw [image_comp, ← add_group.image_closure (to_fun A : A₀ → A)]},
--      congr' 1,
--      apply set.subset.antisymm,
--      { rintros x hx,
--        rw ← span_eq (I^m) at hx,
--        rw span_mul_span at hx,
--        apply span_induction hx,
--        { intro, exact add_group.mem_closure },
--        { apply is_add_submonoid.zero_mem },
--        { intros,
--          apply is_add_submonoid.add_mem, assumption' },
--        { intros a li hli,
--          apply add_group.in_closure.rec_on hli,
--          { rintros _ ⟨⟨l, i⟩, H, rfl⟩,
--            apply add_group.mem_closure,
--            refine ⟨⟨l, a • i⟩, _, _⟩,
--            { rw set.mem_prod at H ⊢,
--              exact ⟨H.1, (I^m).smul_mem a H.2⟩ },
--            { dsimp,
--              erw [← mul_assoc, mul_comm l a, mul_assoc] } },
--          { rw smul_zero,
--            apply is_add_submonoid.zero_mem },
--          { intros,
--            rw smul_neg,
--            apply is_add_subgroup.neg_mem,
--            assumption },
--          { intros,
--            rw smul_add,
--            apply is_add_submonoid.add_mem,
--            assumption' } } },
--      { haveI tmp : is_add_subgroup ↑(span A₀ ↑L * I^m) := submodule.submodule_is_add_subgroup _,
--        apply @add_group.closure_subset _ _ _ _ tmp,
--        rintros _ ⟨⟨l, i⟩, hli, rfl⟩,
--        rw set.mem_prod at hli,
--        exact mul_mem_mul (subset_span hli.1) hli.2, } },
--    { clear this,
--      apply set.subset.antisymm,
--      { let RHS := _,
--        let temp : _ ⊆ RHS := _,
--        exact temp,
--        letI : is_add_subgroup RHS := add_group.closure.is_add_subgroup _,
--        { apply add_group.closure_subset,
--          rintros _ ⟨t, ht, ki, hki, rfl⟩,
--          apply add_group.in_closure.rec_on hki,
--          { rintros _ ⟨k, hk, i, hi, rfl⟩,
--            rw ← mul_assoc,
--            apply add_group.mem_closure,
--            refine ⟨(t * k, i), ⟨set.mem_prod.mpr ⟨add_group.mem_closure _, ‹_›⟩, rfl⟩⟩,
--            exact ⟨t, ht, k, hk, rfl⟩ },
--          all_goals {intros, simp [left_distrib, is_add_submonoid.zero_mem] },
--          { apply is_add_subgroup.neg_mem, assumption },
--          { apply is_add_submonoid.add_mem, assumption' } } },
--      { apply add_group.closure_subset,
--        rintros _ ⟨⟨x, i⟩, hx, rfl⟩,
--        rw set.mem_prod at hx,
--        cases hx with hx hi,
--        change x ∈ _ at hx,
--        change i ∈ _ at hi,
--        change x * i ∈ _,
--        apply add_group.in_closure.rec_on hx,
--        { rintros _ ⟨t, ht, k, hk, rfl⟩,
--          apply add_group.mem_closure,
--          rw mul_assoc,
--          exact ⟨t, ht, k * i, add_group.mem_closure ⟨k, hk, i, hi, rfl⟩, rfl⟩ },
--        all_goals {simp [right_distrib, is_add_submonoid.zero_mem]},
--        { intros, apply is_add_subgroup.neg_mem, assumption },
--        { intros, apply is_add_submonoid.add_mem, assumption' } } } }
end

set_option class.instance_max_depth 150

lemma mul_left (hT : is_open (↑(ideal.span T) : set A)) (a : away T s) (U : open_add_subgroup A) :
  ∃ (V : open_add_subgroup A),
    map (lmul_left ↥D ATs a) (span ↥D (⇑(of_id A ATs) '' V.val)) ≤
      span ↥D (⇑(of_id A ATs) '' U.val) :=
begin
  apply localization.induction_on a,
  intros a' s',
  clear a,
  suffices : ∃ W : open_add_subgroup A, _,
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
  suffices : ∃ V : open_add_subgroup A, _,
  work_on_goal 0 {
    cases this with V hV,
    use V,
    refine le_trans _ (map_mono hW),
    exact hV },
  clear hW U,
  let V : open_add_subgroup A := ⟨_, by apply_instance, mul_T_open _ hT W⟩,
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
(λ U : open_add_subgroup A, span D (of_id A ATs '' U.1))
(directed T s) (mul_left T s hT) (mul_subset T s Huber_ring.nonarchimedean)

instance (hT : is_open (↑(ideal.span T) : set A)) :
  ring_with_zero_nhd ATs :=
of_submodules_comm
(λ U : open_add_subgroup A, span D (of_id A ATs '' U.1))
(directed T s) (mul_left T s hT) (mul_subset T s Huber_ring.nonarchimedean)

section
variables {B : Type*} [comm_ring B] [topological_space B] [topological_ring B]
variables (hB : nonarchimedean B) {f : A → B} [is_ring_hom f] (hf : continuous f)
variables {s_inv : units B} (hs : s_inv.inv = f s)
variables (hT : is_open (↑(ideal.span T) : set A))
variables (hTB : is_power_bounded_subset {x | ∃ t ∈ T, x = f t * s_inv})

include hs
lemma is_unit : is_unit (f s) :=
by rw [← hs, ← units.coe_inv]; exact is_unit_unit _

noncomputable def lift : ATs → B := localization.away.lift f (is_unit s hs)

include hB hf hT hTB
lemma lift_continuous : @continuous _ _ (away.topological_space T s hT) _ (lift T s hs) :=
sorry

end

end away

end Huber_ring
