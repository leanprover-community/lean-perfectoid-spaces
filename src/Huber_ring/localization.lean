import ring_theory.localization
import tactic.tidy
import tactic.ring

import Huber_ring.basic

import for_mathlib.topological_rings
import for_mathlib.algebra
import for_mathlib.submodule
import for_mathlib.subgroup
import for_mathlib.nonarchimedean.basic
import for_mathlib.group

universes u v

local attribute [instance, priority 0] classical.prop_decidable

local attribute [instance] set.pointwise_mul_comm_semiring
local attribute [instance] set.pointwise_mul_action
local attribute [instance] set.pointwise_mul_image_is_semiring_hom

namespace Huber_ring
open localization algebra topological_ring submodule set topological_add_group
variables {A  : Type u} [comm_ring A] [topological_space A] [topological_ring A]
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

instance : has_coe A ATs := ⟨λ a, (of_id A ATs : A → ATs) a⟩

/--An auxiliary subring, used to define the topology on `away T s`-/
def D.aux : set ATs :=
let s_inv : ATs := ((to_units ⟨s, ⟨1, by simp⟩⟩)⁻¹ : units ATs) in
ring.closure (s_inv • of_id A ATs '' T)

local notation `D` := D.aux T s

instance : is_subring D := by delta D.aux; apply_instance

local notation `Dspan` U := span D (of_id A ATs '' (U : set A))

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
  ∃ (U : open_add_subgroup A), (Dspan U) ≤ (Dspan U₁) ⊓ (Dspan U₂) :=
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
lemma left_mul_subset (h : nonarchimedean A) (U : open_add_subgroup A) (a : A) :
  ∃ V : open_add_subgroup A, (a : ATs) • (Dspan V) ≤ (Dspan U) :=
begin
  cases h _ _ with V hV,
  use V,
  work_on_goal 0 {
    erw [smul_singleton, ← span_image, span_le, ← image_comp, ← algebra.map_lmul_left, image_comp],
    refine subset.trans (image_subset (of_id A ATs : A → ATs) _) subset_span,
    rw image_subset_iff,
    exact hV },
  apply mem_nhds_sets (continuous_mul_left _ _ U.is_open),
  rw [mem_preimage_eq, mul_zero],
  exact U.zero_mem
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
  choose s hs using finset.subset_image_iff.mp h,
  use s.bind (λ f, f.frange),
  rcases hs with ⟨hs, rfl⟩,
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
local notation `D` := D.aux T s
local notation `Dspan` U := span D (of_id A ATs '' (U : set A))

set_option class.instance_max_depth 80

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
  -- Observe L ⊆ span T
  have Lsub : (↑(L.image (to_fun A)) : set A) ⊆ ↑(ideal.span T) :=
  by { rw finset.coe_image, exact set.subset.trans (image_subset _ subset_span) hI },
  -- Choose a finite set K such that L ⊆ span (T * K)
  cases K.aux _ _ Lsub with K hK,
  -- Choose V such that K * V ⊆ U
  let nonarch := Huber_ring.nonarchimedean,
  let V := K.inf (λ k : A, classical.some (nonarch.left_mul_subset U k)),
  cases (is_ideal_adic_iff I).mp top with H₁ H₂,
  have hV : ↑K * (V : set A) ⊆ U,
  { rintros _ ⟨k, hk, v, hv, rfl⟩,
    apply classical.some_spec (nonarch.left_mul_subset U k),
    refine ⟨k, set.mem_singleton _, v, _, rfl⟩,
    apply (finset.inf_le hk : V ≤ _),
    exact hv },
  replace hV : span ℤ _ ≤ span ℤ _ := span_mono hV,
  erw [← span_mul_span, ← submodule.smul_def] at hV,
  -- Choose m such that I^m ⊆ V
  cases H₂ _ (mem_nhds_sets (emb.continuous _ V.is_open) _) with m hm,
  work_on_goal 1 {
    erw [mem_preimage_eq, is_ring_hom.map_zero (to_fun A)],
    { exact V.zero_mem },
    apply_instance },
  rw ← image_subset_iff at hm,
  erw [← add_subgroup_eq_spanℤ (V : set A), ← add_subgroup_eq_spanℤ (↑(I^m) : set A₀)] at hm,
  change (submodule.map (alg_hom_int $ to_fun A).to_linear_map _) ≤ _ at hm,
  work_on_goal 1 {apply_instance},
  -- It suffices to provide an open subgroup
  apply @open_add_subgroup.is_open_of_open_add_subgroup A _ _ _ _
    (submodule.submodule_is_add_subgroup _),
  refine ⟨⟨to_fun A '' ↑(I^(m+1)), _, _⟩, _⟩,
  work_on_goal 2 {assumption},
  all_goals { try {apply_instance} },
  { exact embedding_open emb hf (H₁ _) },
  -- And now we start a long calculation
  -- Unfortunately it seems to be hard to express in calc mode
  -- First observe: I^(m+1) = L • I^m as A₀-ideal, but also as ℤ-submodule
  erw [subtype.coe_mk, pow_succ, ← hL, ← submodule.smul_def, hL, smul_eq_smul_spanℤ],
  change (submodule.map (alg_hom_int $ to_fun A).to_linear_map _) ≤ _,
  work_on_goal 1 {apply_instance},
  -- Now we map the above equality through the canonical map A₀ → A
  erw [submodule.map_mul, ← span_image, ← submodule.smul_def],
  erw [finset.coe_image] at hK,
  -- Next observe: L • I^m ≤ (T * K) • V
  refine le_trans (smul_le_smul hK hm) _,
  -- Also observe: T • (K • V) ≤ T • U
  refine (le_trans (le_of_eq _) (smul_le_smul (le_refl T) hV)),
  change span _ _ * _ = _,
  erw [span_span, ← mul_smul],
  refl
end

set_option class.instance_max_depth 80

lemma mul_left.aux₁ (hT : is_open (↑(ideal.span T) : set A)) (U : open_add_subgroup A) :
  ∃ (V : open_add_subgroup A),
    (↑((to_units ⟨s, ⟨1, pow_one s⟩⟩)⁻¹ : units ATs) : ATs) • (Dspan ↑V) ≤ Dspan ↑U :=
begin
  refine ⟨⟨_, mul_T_open _ hT U, by apply_instance⟩, _⟩,
  erw [subtype.coe_mk (↑(T • span ℤ ↑U) : set A), @submodule.smul_def ℤ, span_mul_span],
  change _ • span _ ↑(submodule.map (alg_hom_int $ (of_id A ATs : A → ATs)).to_linear_map _) ≤ _,
  erw [← span_image, span_spanℤ, submodule.smul_def, span_mul_span, span_le],
  rintros _ ⟨s_inv, hs_inv, tu, htu, rfl⟩,
  erw mem_image at htu,
  rcases htu with ⟨_, ⟨t, ht, u, hu, rfl⟩, rfl⟩,
  rw submodule.mem_coe,
  convert (span _ _).smul_mem _ _ using 1,
  work_on_goal 3 { exact subset_span ⟨u, hu, rfl⟩ },
  work_on_goal 1 { constructor },
  work_on_goal 0 {
    change s_inv * (algebra_map _ _) = _ • (algebra_map _ _),
    rw [algebra.map_mul, ← mul_assoc],
    congr },
  { apply ring.mem_closure, exact ⟨s_inv, hs_inv, _, ⟨t, ht, rfl⟩, rfl⟩ }
end

lemma mul_left.aux₂ (hT : is_open (↑(ideal.span T) : set A))
  (s' : powers s) (U : open_add_subgroup A) :
  ∃ (V : open_add_subgroup A),
    (↑((to_units s')⁻¹ : units ATs) : ATs) • (Dspan (V : set A)) ≤ Dspan (U : set A) :=
begin
  rcases s' with ⟨_, ⟨n, rfl⟩⟩,
  induction n with k hk,
  { use U,
    simp only [pow_zero],
    change (1 : ATs) • _ ≤ _,
    rw one_smul,
    exact le_refl _ },
  cases hk with W hW,
  cases mul_left.aux₁ T s hT W with V hV,
  use V,
  refine le_trans _ hW,
  refine le_trans (le_of_eq _) (smul_le_smul (le_refl _) hV),
  change _ = (_ : ATs) • _,
  rw ← mul_smul,
  congr' 1,
  change ⟦((1 : A), _)⟧ = ⟦(1 * 1, _)⟧,
  simpa [pow_succ'],
end

lemma mul_left (hT : is_open (↑(ideal.span T) : set A)) (a : ATs) (U : open_add_subgroup A) :
  ∃ (V : open_add_subgroup A), a • (Dspan (V : set A)) ≤ Dspan (U : set A) :=
begin
  apply localization.induction_on a,
  intros a' s',
  clear a,
  cases mul_left.aux₂ _ _ hT s' U with W hW,
  cases left_mul_subset T s Huber_ring.nonarchimedean W a' with V hV,
  use V,
  erw [localization.mk_eq, mul_comm, mul_smul],
  exact le_trans (smul_le_smul (le_refl _) hV) hW
end

lemma is_basis (hT : is_open (↑(ideal.span T) : set A)) :
  is_subgroups_basis (λ U : open_add_subgroup A, (span D (of_id A ATs '' U.1) : set ATs)) :=
is_subgroups_basis.of_submodules_comm _
  (directed T s) (mul_left T s hT) (mul_le T s Huber_ring.nonarchimedean)

def ring_with_nhds (hT : is_open (↑(ideal.span T) : set A)) :
  ring_with_zero_nhd ATs :=
@is_subgroups_basis.to_ring_with_zero_nhd ATs _ _ _
(λ U : open_add_subgroup A, (span D (of_id A ATs '' U.1) : set ATs)) (away.is_basis T s hT)

def top_space (hT : is_open (↑(ideal.span T) : set A)) : topological_space ATs :=
@ring_with_zero_nhd.topological_space ATs (ring_with_nhds T s hT)

section
variables {B : Type*} [comm_ring B] [topological_space B] [topological_ring B]
variables (hB : nonarchimedean B) {f : A → B} [is_ring_hom f] (hf : continuous f)
variables {fs_inv : units B} (hs : fs_inv.inv = f s)
variables (hT : is_open (↑(ideal.span T) : set A))
variables (hTB : is_power_bounded_subset ((↑fs_inv : B) • f '' T))

include hs
lemma is_unit : is_unit (f s) :=
by rw [← hs, ← units.coe_inv]; exact is_unit_unit _

noncomputable def lift : ATs → B := localization.away.lift f (is_unit s hs)

instance : is_ring_hom (lift T s hs : ATs → B) :=
localization.away.lift.is_ring_hom f _

@[simp] lemma lift_of (a : A) :
  lift T s hs (of a) = f a := localization.away.lift_of _ _ _

@[simp] lemma lift_coe (a : A) :
  lift T s hs a = f a := localization.away.lift_of _ _ _

@[simp] lemma lift_comp_of :
  lift T s hs ∘ of = f := localization.lift'_comp_of _ _ _

-- TODO: this has nothing to do with lift so should perhaps be elsewhere
-- (because KMB keeps confusing it with the next lemma ;-))
lemma of_continuous (hT : is_open (↑(ideal.span T) : set A)) :
  @continuous _ _ _ (away.top_space T s hT) (of : A → ATs) :=
begin
  apply is_subgroups_basis.continuous_into _,
  all_goals {try {apply_instance}},
  intro U,
  apply open_add_subgroup.is_open_of_open_add_subgroup _,
  all_goals {try {apply_instance}},
  { use U,
    rw ← image_subset_iff,
    exact subset_span },
  { apply is_add_group_hom.preimage _ _,
    all_goals {apply_instance} }
end

include hB hf hT hTB
lemma lift_continuous : @continuous _ _ (away.top_space T s hT) _ (lift T s hs) :=
begin
  apply continuous_of_continuous_at_zero _ _,
  all_goals {try {apply_instance}},
  apply is_subgroups_basis.is_topological_add_group,
  intros U hU,
  rw is_ring_hom.map_zero (lift T s hs) at hU,
  rw filter.mem_map_sets_iff,
  let hF := power_bounded.ring.closure' hB _ hTB,
  erw is_bounded_add_subgroup_iff hB at hF,
  rcases hF U hU with ⟨V, hVF⟩,
  let hV := V.mem_nhds_zero,
  rw ← is_ring_hom.map_zero f at hV,
  replace hV := hf.tendsto 0 hV,
  rw filter.mem_map_sets_iff at hV,
  rcases hV with ⟨W, hW, hWV⟩,
  cases Huber_ring.nonarchimedean W hW with Y hY,
  refine ⟨↑(Dspan Y), _, _⟩,
  { apply mem_nhds_sets,
    { convert is_subgroups_basis.is_op _ Y },
    { exact (Dspan ↑Y).zero_mem } },
  { refine set.subset.trans _ hVF,
    rintros _ ⟨x, hx, rfl⟩,
    apply span_induction hx,
    { rintros _ ⟨a, ha, rfl⟩,
      erw [lift_of, ← mul_one (f a)],
      refine mul_mem_mul (subset_span $ hWV $ ⟨a, hY ha, rfl⟩)
        (subset_span $ is_submonoid.one_mem _) },
    { rw is_ring_hom.map_zero (lift T s hs),
      exact is_add_submonoid.zero_mem _ },
    { intros a b ha hb,
      rw is_ring_hom.map_add (lift T s hs),
      exact is_add_submonoid.add_mem ha hb },
    { rw [submodule.smul_def, span_mul_span],
      intros d a ha,
      rw [(show d • a = ↑d * a, from rfl), is_ring_hom.map_mul (lift T s hs), mul_comm],
      rcases mem_span_iff_lc.mp ha with ⟨l, hl₁, hl₂⟩,
      rw lc.mem_supported at hl₁,
      rw [← hl₂, lc.total_apply] at ha ⊢,
      rw finsupp.sum_mul,
      apply sum_mem_span,
      intros b hb',
      show (↑(_ : ℤ) * _) * _ ∈ _,
      rcases hl₁ hb' with ⟨v, hv, b, hb, rfl⟩,
      refine ⟨↑(l (v * b)) * v, _, b * lift T s hs ↑d, _, _⟩,
      { rw ← gsmul_eq_mul, exact is_add_subgroup.gsmul_mem hv },
      { refine is_submonoid.mul_mem hb _,
        cases d with d hd,
        rw subtype.coe_mk,
        apply ring.in_closure.rec_on hd,
        { rw is_ring_hom.map_one (lift T s hs), exact is_submonoid.one_mem _ },
        { rw [is_ring_hom.map_neg (lift T s hs), is_ring_hom.map_one (lift T s hs)],
          exact is_add_subgroup.neg_mem (is_submonoid.one_mem _) },
        { rintros _ ⟨sinv, hsinv, _, ⟨t, ht, rfl⟩, rfl⟩ b hb,
          rw is_ring_hom.map_mul (lift T s hs),
          refine is_submonoid.mul_mem _ hb,
          apply ring.mem_closure,
          erw [is_ring_hom.map_mul (lift T s hs), lift_of],
          refine ⟨_, _, _, ⟨t, ht, rfl⟩, rfl⟩,
          rw mem_singleton_iff at hsinv ⊢,
          subst hsinv,
          erw [← units.coe_map (lift T s hs), ← units.ext_iff, is_group_hom.map_inv (units.map _),
            inv_eq_iff_inv_eq, units.ext_iff, units.coe_inv, hs],
          { symmetry, exact lift_of T s hs s },
          { apply_instance } },
        { intros a b ha hb,
          rw is_ring_hom.map_add (lift T s hs),
          exact is_add_submonoid.add_mem ha hb } },
      { repeat {rw mul_assoc} } } }
end

end

end away

end Huber_ring
