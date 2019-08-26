import ring_theory.localization
import tactic.tidy
import tactic.ring

import Huber_ring.basic

import for_mathlib.topological_rings
import for_mathlib.algebra
import for_mathlib.submodule
import for_mathlib.nonarchimedean.basic
import for_mathlib.group
import for_mathlib.open_subgroup

/-!
This file covers (a special case of) Wedhorn's Proposition and Definition 5.51.
Starting with a Huber ring `A`, `s ∈ A` and `T ⊆ A`, we construct a (nonarchimedean)
topological ring `A⟮T/s⟯` and a map `coe : A → A⟮T/s⟯` such that `s` becomes invertibles
and `{t/s ; t ∈ T}` is power-bounded in `A⟮T/s⟯`. In addition `A⟮T/s⟯` is universal for these
properties. Algebraically, `A⟮T/s⟯` is simply the localization `s⁻¹A`, but the topology does
depend on `T`. In Wedhorn, the setup is slighly more general because the single element `s`
is replaced by a family of elements. The case covered here will be sufficient for our purposes.

In view of our applications in Spa.lean, we assume right away that T is finite and generates
an open ideal in A.
-/

universes u v

local attribute [instance, priority 0] classical.prop_decidable

local attribute [instance] set.pointwise_mul_comm_semiring
local attribute [instance] set.pointwise_mul_action
local attribute [instance] set.pointwise_mul_image_is_semiring_hom

local notation `𝓝` x: 70 := nhds x

namespace Huber_ring
open localization algebra topological_ring submodule set topological_add_group
variables (A  : Type u) [comm_ring A] [topological_space A] [topological_ring A]

/-
Our goal is to define a topology on (away s), which is the localization of A at s.
This topology will depend on T, and should not depend on the ring of definition.
In the literature, this ring is commonly denoted with A(T/s) to indicate the
dependence on T. See discussion in Wedhorn starting around Proposition 5.51
-/

/-- The package needed to define a rational open subset R(T/s) of Spa(A) -/
structure rational_open_data :=
(s : A)
(T : set A)
[Tfin : fintype T]
(Hopen : is_open (ideal.span T).carrier)

variables {A}

/-- Topological localization A(T/s) -/
def rational_open_data.top_loc (r : rational_open_data A) := away r.s

protected def rational_open_data.ideal (r : rational_open_data A) := ideal.span r.T

-- useless?
lemma rational_open_data.is_open_ideal (r : rational_open_data A) : is_open r.ideal.carrier :=
r.Hopen

namespace top_loc
variables (r : rational_open_data A)

local notation `A⟮T/s⟯` := r.top_loc

meta def find_inst : tactic unit := `[delta rational_open_data.top_loc away; apply_instance]

instance : comm_ring A⟮T/s⟯ := by find_inst

instance : module A A⟮T/s⟯ := by find_inst

instance : algebra A A⟮T/s⟯ := by find_inst

instance : has_coe A A⟮T/s⟯ := ⟨λ a, (of_id A A⟮T/s⟯ : A → A⟮T/s⟯) a⟩

@[elim_cast]
lemma coe_zero: coe (0 : A) = (0 : A⟮T/s⟯) :=
is_ring_hom.map_zero _

/--An auxiliary subring, used to define the topology on `away T s`-/
def D.aux : set A⟮T/s⟯ :=
let s_inv : A⟮T/s⟯ := ((to_units ⟨r.s, ⟨1, by simp⟩⟩)⁻¹ : units A⟮T/s⟯) in
ring.closure (s_inv • (coe : A → A⟮T/s⟯) '' r.T)

local notation `D` := D.aux r

instance : is_subring D := by delta D.aux; apply_instance

local notation `Dspan` U := span D ((coe : A → A⟮T/s⟯) '' (U : set A))

/-
To put a topology on `A⟮T/s⟯` we want to use the construction
`topology_of_submodules_comm` which needs a directed family of
submodules of `A⟮T/s⟯` viewed as `D`-algebra.
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
  ∃ V : open_add_subgroup A, (a : A⟮T/s⟯) • (Dspan V) ≤ (Dspan U) :=
begin
  cases h _ _ with V hV,
  use V,
  work_on_goal 0 {
    erw [smul_singleton, ← span_image, span_le, ← image_comp, ← algebra.map_lmul_left, image_comp],
    refine subset.trans (image_subset (coe: A → A⟮T/s⟯) _) subset_span,
    rw image_subset_iff,
    exact hV },
  apply mem_nhds_sets (continuous_mul_left _ _ U.is_open),
  rw [mem_preimage, mul_zero],
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
  rw ← is_semiring_hom.map_mul (image (coe : A → A⟮T/s⟯)),
  exact image_subset _ hV,
end

lemma K.aux (L : finset A) (h : (↑L : set A) ⊆ r.ideal) :
  ∃ (K : finset A), (↑L : set A) ⊆ (↑(span ℤ (r.T * ↑K)) : set A) :=
begin
  unfold rational_open_data.ideal at h,
  delta ideal.span at h,
  rw [← set.image_id r.T] at h,
  erw finsupp.span_eq_map_total at h,
  choose s hs using finset.subset_image_iff.mp h,
  use s.bind (λ f, f.frange),
  rcases hs with ⟨hs, rfl⟩,
  intros l hl,
  rcases finset.mem_image.mp hl with ⟨f, hf, rfl⟩,
  refine is_add_submonoid.finset_sum_mem ↑(span _ _) _ _ _,
  intros t ht,
  refine subset_span ⟨t, _, _, _, mul_comm _ _⟩,
  { replace hf := hs hf,
    erw finsupp.mem_supported A f at hf,
    exact hf ht },
  { erw [linear_map.id_apply, finset.mem_bind],
    use [f, hf],
    erw finsupp.mem_support_iff at ht,
    erw finsupp.mem_frange,
    exact ⟨ht, ⟨t, rfl⟩⟩ }
end

end top_loc

end Huber_ring

namespace Huber_ring
open localization algebra topological_ring submodule set topological_add_group
variables {A  : Type u} [Huber_ring A]
variables (r : rational_open_data A)

namespace rational_open_data

local notation `A⟮T/s⟯` := r.top_loc
local notation `D` := top_loc.D.aux r
local notation `Dspan` U := span D ((coe : A → A⟮T/s⟯) '' (U : set A))

set_option class.instance_max_depth 80

/- Wedhorn 6.20 for n = 1-/
lemma mul_T_open (U : open_add_subgroup A) : is_open (↑(r.T • span ℤ (U : set A)) : set A) :=
begin
  suffices : (↑(r.T • span ℤ (U : set A)) : set A) ∈ nhds (0 : A),
    from (open_add_subgroup.of_mem_nhds A this).is_open,
  sorry,
  /-
  refine open_add_subgroup.is_open_of_nonempty_open_subset _,
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
    erw [mem_preimage, is_ring_hom.map_zero (to_fun A)],
    { exact V.zero_mem },
    apply_instance },
  rw ← image_subset_iff at hm,
  erw [← add_subgroup_eq_span_int (V : set A), ← add_subgroup_eq_span_int (↑(I^m) : set A₀)] at hm,
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
  erw [subtype.coe_mk, pow_succ, ← hL, ← submodule.smul_def, hL, smul_eq_smul_span_int],
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
  -/
end

set_option class.instance_max_depth 80

lemma mul_left.aux₁ (U : open_add_subgroup A) :
  ∃ (V : open_add_subgroup A),
    (↑((to_units ⟨r.s, ⟨1, pow_one r.s⟩⟩)⁻¹ : units A⟮T/s⟯) : A⟮T/s⟯) • (Dspan ↑V) ≤ Dspan ↑U :=
begin
  refine ⟨⟨_, mul_T_open r U, by apply_instance⟩, _⟩,
  erw [subtype.coe_mk (↑(r.T • span ℤ ↑U) : set A), @submodule.smul_def ℤ, span_mul_span],
  change _ • span _ ↑(submodule.map (alg_hom_int $ (of_id A A⟮T/s⟯ : A → A⟮T/s⟯)).to_linear_map _) ≤ _,
  erw [← span_image, span_span_int, submodule.smul_def, span_mul_span, span_le],
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

lemma mul_left.aux₂ (s' : powers r.s) (U : open_add_subgroup A) :
  ∃ (V : open_add_subgroup A),
    (↑((to_units s')⁻¹ : units A⟮T/s⟯) : A⟮T/s⟯) • (Dspan (V : set A)) ≤ Dspan (U : set A) :=
begin
  rcases s' with ⟨_, ⟨n, rfl⟩⟩,
  induction n with k hk,
  { use U,
    simp only [pow_zero],
    change (1 : A⟮T/s⟯) • _ ≤ _,
    rw one_smul,
    exact le_refl _ },
  cases hk with W hW,
  cases mul_left.aux₁ r W with V hV,
  use V,
  refine le_trans _ hW,
  refine le_trans (le_of_eq _) (smul_le_smul (le_refl _) hV),
  change _ = (_ : A⟮T/s⟯) • _,
  rw ← mul_smul,
  congr' 1,
  change ⟦((1 : A), _)⟧ = ⟦(1 * 1, _)⟧,
  simpa [pow_succ'],
end

lemma mul_left (a : A⟮T/s⟯) (U : open_add_subgroup A) :
  ∃ (V : open_add_subgroup A), a • (Dspan (V : set A)) ≤ Dspan (U : set A) :=
begin
  apply localization.induction_on a,
  intros a' s',
  clear a,
  cases mul_left.aux₂ _ s' U with W hW,
  cases top_loc.left_mul_subset r Huber_ring.nonarchimedean W a' with V hV,
  use V,
  erw [localization.mk_eq, mul_comm, mul_smul],
  exact le_trans (smul_le_smul (le_refl _) hV) hW
end

def top_loc_basis : subgroups_basis A⟮T/s⟯ :=
subgroups_basis.of_indexed_submodules_of_comm
  (λ U : open_add_subgroup A, (span D (coe '' U.1)))
  (top_loc.directed r) (mul_left r) (top_loc.mul_le r Huber_ring.nonarchimedean)

local attribute [instance] top_loc_basis

def top_space : topological_space A⟮T/s⟯ :=
subgroups_basis.topology A⟮T/s⟯

local attribute [instance] top_space

def top_ring : topological_ring A⟮T/s⟯ :=
ring_filter_basis.topological_ring _

local attribute [instance] top_ring

lemma mem_nhds_zero {V : set A⟮T/s⟯} :
  V ∈ 𝓝 (0 : A⟮T/s⟯) ↔ ∃ U : open_add_subgroup A, (span D (coe '' U.1)).carrier ⊆ V :=
begin
  rw subgroups_basis.mem_nhds_zero,
  split ; intro h,
  { rcases h with ⟨G, ⟨U, hG⟩, hG'⟩,
    use U,
    convert hG' },
  { rcases h with ⟨U, hU⟩,
    exact ⟨_, mem_range_self _, hU⟩ },
end

-- Still part of Wedhorn 5.51
-- TODO? Rename continuous_coe
lemma of_continuous :
  continuous (coe : A → A⟮T/s⟯) :=
begin
  suffices : continuous_at (coe : A → A⟮T/s⟯) 0,
    from topological_add_group.continuous_of_continuous_at_zero _ this,
  unfold continuous_at,
  rw subgroups_basis.tendsto_into,
  rintros _ ⟨U, rfl⟩,
  suffices : coe ⁻¹' (Dspan U.val).carrier ∈ 𝓝 (0 : A),
  { simpa only [top_loc.coe_zero, sub_zero] using this },
  apply filter.mem_sets_of_superset (open_add_subgroup.mem_nhds_zero U),
  rw ← image_subset_iff,
  exact subset_span
end

section

-- We now derive the universal property of `coe : A → A⟮T/s⟯`, still part of Wedhorn 5.51

variables {B : Type*} [comm_ring B] [topological_space B] [topological_ring B]
variables (hB : nonarchimedean B) {f : A → B} [is_ring_hom f] (hf : continuous f)
variables {fs_inv : units B} (hs : fs_inv.inv = f r.s)
variables (hTB : is_power_bounded_subset ((↑fs_inv : B) • f '' r.T))

include hs
lemma is_unit : is_unit (f r.s) :=
by rw [← hs, ← units.coe_inv]; exact is_unit_unit _

noncomputable def lift : A⟮T/s⟯ → B := localization.away.lift f (is_unit r hs)

instance : is_ring_hom (r.lift hs : A⟮T/s⟯ → B) :=
localization.away.lift.is_ring_hom f _

@[simp] lemma lift_of (a : A) :
  r.lift hs (of a) = f a := localization.away.lift_of _ _ _

@[simp] lemma lift_coe (a : A) :
  r.lift hs a = f a := localization.away.lift_of _ _ _

@[simp] lemma lift_comp_of :
  r.lift hs ∘ of = f := localization.lift'_comp_of _ _ _


include hB hf hTB
lemma lift_continuous : continuous (r.lift hs) :=
begin
  refine continuous_of_continuous_at_zero _ _,
  intros U hU,
  rw is_ring_hom.map_zero (r.lift hs) at hU,
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
    { convert subgroups_basis.is_op _ rfl _,
      apply mem_range_self,  },
    { exact (Dspan ↑Y).zero_mem } },
  { refine set.subset.trans _ hVF,
    rintros _ ⟨x, hx, rfl⟩,
    apply span_induction hx,
    { rintros _ ⟨a, ha, rfl⟩,
      erw [lift_of, ← mul_one (f a)],
      refine mul_mem_mul (subset_span $ hWV $ ⟨a, hY ha, rfl⟩)
        (subset_span $ is_submonoid.one_mem _) },
    { rw is_ring_hom.map_zero (r.lift hs),
      exact is_add_submonoid.zero_mem _ },
    { intros a b ha hb,
      rw is_ring_hom.map_add (r.lift hs),
      exact is_add_submonoid.add_mem ha hb },
    { rw [submodule.smul_def, span_mul_span],
      intros d a ha,
      rw [(show d • a = ↑d * a, from rfl), is_ring_hom.map_mul (r.lift hs), mul_comm],
      rcases (finsupp.mem_span_iff_total ℤ).mp (by rw set.image_id; exact ha) with ⟨l, hl₁, hl₂⟩,
      rw finsupp.mem_supported at hl₁,
      rw [← hl₂, finsupp.total_apply] at ha ⊢,
      rw finsupp.sum_mul,
      refine is_add_submonoid.finset_sum_mem ↑(span _ _) _ _ _,
      intros b hb',
      apply subset_span,
      show (↑(_ : ℤ) * _) * _ ∈ _,
      rcases hl₁ hb' with ⟨v, hv, b, hb, rfl⟩,
      refine ⟨↑(l (v * b)) * v, _, b * r.lift hs ↑d, _, _⟩,
      { rw ← gsmul_eq_mul, exact is_add_subgroup.gsmul_mem hv },
      { refine is_submonoid.mul_mem hb _,
        cases d with d hd,
        rw subtype.coe_mk,
        apply ring.in_closure.rec_on hd,
        { rw is_ring_hom.map_one (r.lift hs), exact is_submonoid.one_mem _ },
        { rw [is_ring_hom.map_neg (r.lift hs), is_ring_hom.map_one (r.lift hs)],
          exact is_add_subgroup.neg_mem (is_submonoid.one_mem _) },
        { rintros _ ⟨sinv, hsinv, _, ⟨t, ht, rfl⟩, rfl⟩ b hb,
          rw is_ring_hom.map_mul (r.lift hs),
          refine is_submonoid.mul_mem _ hb,
          apply ring.mem_closure,
          erw [is_ring_hom.map_mul (r.lift hs), lift_of],
          refine ⟨_, _, _, ⟨t, ht, rfl⟩, rfl⟩,
          rw mem_singleton_iff at hsinv ⊢,
          subst hsinv,
          erw [← units.coe_map (r.lift hs), ← units.ext_iff, is_group_hom.map_inv (units.map _),
            inv_eq_iff_inv_eq, units.ext_iff, units.coe_inv, hs],
          { symmetry, exact r.lift_of hs r.s },
          { apply_instance } },
        { intros a b ha hb,
          rw is_ring_hom.map_add (r.lift hs),
          exact is_add_submonoid.add_mem ha hb } },
      { simp [mul_assoc] } } }
end

end

end rational_open_data

end Huber_ring
