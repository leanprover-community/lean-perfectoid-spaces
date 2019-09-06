import for_mathlib.topological_field
import for_mathlib.topology
import for_mathlib.uniform_space.uniform_field
import valuation.topology
import valuation.with_zero_topology
import topology.algebra.ordered

/-!
In this file we study the topology of a field `K` endowed with a valuation (in our application
to adic spaces, `K` will be the valuation field associated to some valuation on a ring, defined in
valuation.basic).

We already know from valuation.topology that one can build a topology on `K` which
makes it a topological ring.

The first goal is to show `K` is a topological *field*, ie inversion is continuous
at every non-zero element.

The next goal is to prove `K` is a *completable* topological field. This gives us
a completion `hat K` which is a topological field. We also prove that `K` is automatically
separated, so the map from `K` to `hat K` is injective.

Then we extend the valuation given on `K` to a valuation on `hat K`.
-/

open filter set linear_ordered_structure

local attribute [instance, priority 0] classical.decidable_linear_order

local notation `𝓝` x: 70 := nhds x

section division_ring

variables {K : Type*} [division_ring K]


section valuation_topological_division_ring

section inversion_estimate
variables {Γ : Type*} [linear_ordered_comm_group_with_zero Γ] (v : valuation K Γ)

-- The following is the main technical lemma ensuring that inversion is continuous
-- in the topology induced by a valuation on a division ring (ie the next instance)
-- and the fact that a valued field is completable
-- [BouAC, VI.5.1 Lemme 1]
lemma valuation.inversion_estimate {x y : K} {γ : units Γ} (y_ne : y ≠ 0)
  (h : v (x - y) < min (γ * ((v y) * (v y))) (v y)) :
  v (x⁻¹ - y⁻¹) < γ :=
begin
  have hyp1 : v (x - y) < γ * ((v y) * (v y)),
    from lt_of_lt_of_le h (min_le_left _ _),
  have hyp1' : v (x - y) * ((v y) * (v y))⁻¹ < γ,
    from mul_inv_lt_of_lt_mul' hyp1,
  have hyp2 : v (x - y) < v y,
    from lt_of_lt_of_le h (min_le_right _ _),
  have key : v x = v y, from valuation.map_eq_of_sub_lt v hyp2,
  have x_ne : x ≠ 0,
  { intro h,
    apply y_ne,
    rw [h, v.map_zero] at key,
    exact v.zero_iff.1 key.symm },
  have decomp : x⁻¹ - y⁻¹ = x⁻¹ * (y - x) * y⁻¹,
  by rw [mul_sub_left_distrib, sub_mul, mul_assoc,
        show y * y⁻¹ = 1, from mul_inv_cancel y_ne,
        show x⁻¹ * x = 1, from inv_mul_cancel x_ne, mul_one, one_mul],
  calc
    v (x⁻¹ - y⁻¹) = v (x⁻¹ * (y - x) * y⁻¹) : by rw decomp
    ... = (v x⁻¹) * (v $ y - x) * (v y⁻¹) : by repeat { rw valuation.map_mul }
    ... = (v x)⁻¹ * (v $ y - x) * (v y)⁻¹ : by rw [v.map_inv' x_ne, v.map_inv' y_ne]
    ... = (v $ y - x) * ((v y) * (v y))⁻¹ : by
      rw [mul_assoc, mul_comm, key, mul_assoc, ← group_with_zero.mul_inv_rev]
    ... = (v $ y - x) * ((v y) * (v y))⁻¹ : rfl
    ... = (v $ x - y) * ((v y) * (v y))⁻¹ : by rw valuation.map_sub_swap
    ... < γ : hyp1',
end
end inversion_estimate

local attribute [instance] valued.subgroups_basis subgroups_basis.topology
  ring_filter_basis.topological_ring

local notation `v` := valued.value

/-- The topology coming from a valuation on a division rings make it a topological division ring
    [BouAC, VI.5.1 middle of Proposition 1] -/
instance valued.topological_division_ring [valued K] : topological_division_ring K :=
{ continuous_inv :=
    begin
      intros x x_ne s s_in,
      cases valued.mem_nhds.mp s_in with γ hs, clear s_in,
      rw [mem_map, valued.mem_nhds],
      change ∃ (γ : units (valued.Γ K)), {y : K | v (y - x) < γ} ⊆ {x : K | x⁻¹ ∈ s},
      have vx_ne := (valuation.ne_zero_iff $ valued.v K).mpr x_ne,
      let γ' := group_with_zero.mk₀ _ vx_ne,
      -- have : ∃ γ' : units (valued.Γ K), v x = γ', from valuation.unit_is_some (valued.v K) (units.mk0 _ x_ne),
      -- cases this with γ' H,
      use min (γ * (γ'*γ')) γ',
      intros y y_in,
      apply hs,
      change v (y⁻¹ - x⁻¹) < γ,
      simp only [mem_set_of_eq] at y_in,
-- and the fact that a valued field is completable
      rw [coe_min, units.coe_mul, units.coe_mul] at y_in,
      exact valuation.inversion_estimate _ x_ne y_in
    end,
  ..(by apply_instance : topological_ring K) }

section
local attribute [instance] with_zero.topological_space with_zero.regular_space with_zero.nhds_basis

lemma valued.continuous_valuation [valued K] : continuous (v : K → valued.Γ K) :=
begin
  rw continuous_iff_continuous_at,
  intro x,
  classical,
  by_cases h : x = 0,
  { rw h,
    change tendsto _ _ (𝓝 (valued.v K 0)),
    erw valuation.map_zero,
    rw with_zero.tendsto_zero,
    intro γ,
    rw valued.mem_nhds_zero,
    use [γ, set.subset.refl _] },
  { change tendsto _ _ _,
    have v_ne : v x ≠ 0, from (valuation.ne_zero_iff _).mpr h,
    rw with_zero.tendsto_nonzero v_ne,
    apply valued.loc_const v_ne },
end
end

section
-- until the end of this section, all linearly ordered commutative groups will be endowed with
-- the discrete topology
--local attribute [instance] discrete_ordered_comm_group

--local attribute [instance] ordered_comm_group_is_discrete

-- In the next lemma, K will be endowed with its left uniformity coming from the valuation topology
local attribute [instance] valued.uniform_space

instance valued_ring.separated [valued K] : separated K :=
begin
  apply topological_add_group.separated_of_zero_sep,
  intros x x_ne,
  refine ⟨{k | v k < v x}, _, λ h, lt_irrefl _ h⟩,
  rw valued.mem_nhds,
  have : ∃ γ : valued.Γ K, v x = γ, from valuation.unit_is_some (valued.v K) (units.mk0 _ x_ne),
  cases this with γ H,
  exact ⟨γ, λ y hy, by simpa [H] using hy⟩
end

end
end valuation_topological_division_ring

end division_ring

section valuation_on_valued_field_completion
open uniform_space
-- In this section K is commutative (hence a field), and equipped with a valuation
variables {K : Type*} [discrete_field K] [vK : valued K]
include vK

open valued

local notation `v` := valued.value
local notation `Γ₀` R := with_zero (Γ R)

-- until the end of this section, all linearly ordered commutative groups will be endowed with
-- the discrete topology
--local attribute [instance] discrete_ordered_comm_group ordered_comm_group_is_discrete

local attribute [instance, priority 0] valued.uniform_space valued.uniform_add_group

local notation `hat` K := completion K

set_option class.instance_max_depth 300

-- The following instances helps going over the uniform_add_group/topological_add_group loop
def hatK_top_group : topological_add_group (hat K) := uniform_add_group.to_topological_add_group
local attribute [instance] hatK_top_group

def hatK_top_monoid : topological_add_monoid (hat K) :=
topological_add_group.to_topological_add_monoid _
local attribute [instance] hatK_top_monoid

instance valued.completable : completable_top_field K :=
{ separated := by apply_instance,
  nice := begin
    rintros F hF h0,
    have : ∃ (γ₀ : Γ K) (M ∈ F), ∀ x ∈ M, v x ≥ γ₀,
    { rcases (filter.inf_eq_bot_iff _ _).1 h0 with ⟨U, U_in, M, M_in, H⟩,
      rcases valued.mem_nhds_zero.mp U_in with ⟨γ₀, hU⟩,
      existsi [γ₀, M, M_in],
      intros x xM,
      apply le_of_not_lt _,
      intro hyp,
      have : x ∈ U ∩ M := ⟨hU hyp, xM⟩,
      rwa H at this },
    rcases this with ⟨γ₀, M₀, M₀_in, H₀⟩,
    rw valued.cauchy_iff at hF ⊢,
    refine ⟨map_ne_bot hF.1, _⟩,
    replace hF := hF.2,
    intros γ,
    rcases hF (min (γ * γ₀ * γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩, clear hF,
    use (λ x : K, x⁻¹) '' (M₀ ∩ M₁),
    split,
    { rw mem_map,
      apply mem_sets_of_superset (filter.inter_mem_sets M₀_in M₁_in),
      exact subset_preimage_image _ _ },
    { rintros _ _ ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩ ⟨y, ⟨y_in₀, y_in₁⟩, rfl⟩,
      simp only [mem_set_of_eq],
      specialize H₁ x y x_in₁ y_in₁,
      replace x_in₀ := H₀ x x_in₀,
      replace y_in₀ := H₀ y y_in₀, clear H₀,
      apply valuation.inversion_estimate,
      { have : v x ≠ 0,
        { intro h, rw h at x_in₀, exact with_zero.not_coe_le_zero γ₀ x_in₀ },
        exact (valuation.ne_zero_iff _).mp this },
      { refine lt_of_lt_of_le H₁ _,
        rw with_zero.coe_min,
        apply min_le_min _ x_in₀,
        rw mul_assoc,
        rw ← with_zero.mul_coe,
        have : ((γ₀ * γ₀ : Γ K) : Γ₀ K) ≤ v x * v x,
          from calc ↑γ₀ * ↑γ₀ ≤ ↑γ₀ * v x :   actual_ordered_comm_monoid.mul_le_mul_left' x_in₀
                          ... ≤ _ : actual_ordered_comm_monoid.mul_le_mul_right' x_in₀,
        exact actual_ordered_comm_monoid.mul_le_mul_left' this } }
  end  }

local attribute [instance] with_zero.topological_space with_zero.regular_space with_zero.nhds_basis
with_zero.t2_space with_zero.ordered_topology

noncomputable def valued.extension : (hat K) → Γ₀ K :=
completion.dense_inducing_coe.extend (v : K → Γ₀ K)

lemma valued.continuous_extension : continuous (valued.extension : (hat K) → Γ₀ K) :=
 begin
  refine completion.dense_inducing_coe.continuous_extend _,
  intro x₀,
  by_cases h : x₀ = coe 0,
  { refine ⟨0, _⟩,
    erw [h, ← completion.dense_inducing_coe.to_inducing.nhds_eq_comap]; try { apply_instance },
    rw with_zero.tendsto_zero,
    intro γ₀,
    rw valued.mem_nhds,
    exact ⟨γ₀, by simp⟩ },
  { have preimage_one : v ⁻¹' {(1 : Γ₀ K)} ∈ 𝓝 (1 : K),
    { have : v (1 : K) ≠ 0, { rw valued.map_one, exact zero_ne_one.symm },
      convert valued.loc_const this,
      ext x,
      rw [valued.map_one, mem_preimage, mem_singleton_iff, mem_set_of_eq] },
    have : ∃ V ∈ 𝓝 (1 : hat K), ∀ x : K, (x : hat K) ∈ V → v x = 1,
    { rwa [completion.dense_inducing_coe.nhds_eq_comap, mem_comap_sets] at preimage_one,
      rcases preimage_one with ⟨V, V_in, hV⟩,
      use [V, V_in],
      intros x x_in,
      specialize hV x_in,
      rwa [mem_preimage, mem_singleton_iff] at hV },
    rcases this with ⟨V, V_in, hV⟩, --TODO: bump mathlib and use `obtain`

    have : ∃ V' ∈ (𝓝 (1 : hat K)), (0 : hat K) ∉ V' ∧ ∀ x y ∈ V', x*y⁻¹ ∈ V,
    { have : tendsto (λ p : (hat K) × hat K, p.1*p.2⁻¹) ((𝓝 1).prod 𝓝 1) 𝓝 1,
      { rw ← nhds_prod_eq,
        conv {congr, skip, skip, rw ← (one_mul (1 : hat K))},
        refine tendsto_mul continuous_fst.continuous_at (tendsto.comp _ continuous_snd.continuous_at),
        convert topological_division_ring.continuous_inv (1 : hat K) zero_ne_one.symm,
        exact inv_one.symm },
      rcases tendsto_prod_self_iff.mp this V V_in with ⟨U, U_in, hU⟩,
      let hatKstar := (-{0} : set $ hat K),
      have : hatKstar ∈ 𝓝 (1 : hat K),
      { haveI : t1_space (hat K) := @t2_space.t1_space (hat K) _ (@separated_t2 (hat K) _ _),
        exact compl_singleton_mem_nhds zero_ne_one.symm },
      use  [U ∩ hatKstar, filter.inter_mem_sets U_in this],
      split,
      { rintro ⟨h, h'⟩,
        rw mem_compl_singleton_iff at h',
        exact h' rfl },
      { rintros x y ⟨hx, _⟩ ⟨hy, _⟩,
        apply hU ; assumption } },
    rcases this with ⟨V', V'_in, zeroV', hV'⟩,
    have nhds_right : (λ x, x*x₀) '' V' ∈ 𝓝 x₀,
    { have l : function.left_inverse (λ (x : hat K), x * x₀⁻¹) (λ (x : hat K), x * x₀),
      { intro x,
        simp only [mul_assoc, mul_inv_cancel h, mul_one] },
      have r: function.right_inverse (λ (x : hat K), x * x₀⁻¹) (λ (x : hat K), x * x₀),
      { intro x,
        simp only [mul_assoc, inv_mul_cancel h, mul_one] },
      have c : continuous  (λ (x : hat K), x * x₀⁻¹),
        from continuous_mul continuous_id continuous_const,
      rw image_eq_preimage_of_inverse l r,
      rw ← mul_inv_cancel h at V'_in,
      exact c.continuous_at V'_in },
    have : ∃ (z₀ : K) (y₀ ∈ V'), coe z₀ = y₀*x₀ ∧ z₀ ≠ 0,
    { -- TODO add next line to mathlib main completion file
      have : dense_range (coe : K → hat K) := (dense_range_iff_closure_eq _).mpr completion.dense,

      rcases dense_range.mem_nhds this nhds_right with ⟨z₀, y₀, y₀_in, h⟩,
      refine ⟨z₀, y₀, y₀_in, ⟨h.symm, _⟩⟩,
      intro hz,
      rw hz at h,
      cases discrete_field.eq_zero_or_eq_zero_of_mul_eq_zero _ _ h ; finish },
    rcases this with ⟨z₀, y₀, y₀_in, hz₀, z₀_ne⟩,
    have vz₀_ne: valued.v K z₀ ≠ 0,
    { change valued.v K (units.mk0 z₀ z₀_ne) ≠ 0,
      apply valuation.map_unit_ne_zero },
    refine ⟨valued.v K z₀, _⟩,
    rw [with_zero.tendsto_nonzero vz₀_ne, mem_comap_sets],
    use [(λ x, x*x₀) '' V', nhds_right],
    intros x x_in,
    rcases mem_preimage.1 x_in with ⟨y, y_in, hy⟩, clear x_in,
    change y*x₀ = coe x at hy,
    have : valued.v K (x*z₀⁻¹) = 1,
    { apply hV,
      rw [completion.coe_mul, is_field_hom.map_inv' (coe : K → hat K) z₀_ne, ← hy, hz₀, mul_inv'],
      assoc_rw mul_inv_cancel h,
      rw mul_one,
      solve_by_elim },
    calc   valued.v K x = valued.v K (x*z₀⁻¹*z₀) : by rw [mul_assoc, inv_mul_cancel z₀_ne, mul_one]
      ... = valued.v K (x*z₀⁻¹)*valued.v K z₀ : valuation.map_mul _ _ _
      ... = valued.v K z₀ : by rw [this, one_mul]  },
end

@[elim_cast]
lemma valued.extension_extends (x : K) : valued.extension (x : hat K) = v x :=
begin
  haveI : t2_space (with_zero (valued.Γ K)) := regular_space.t2_space _,
  exact completion.dense_inducing_coe.extend_eq_of_cont valued.continuous_valuation x
end

lemma valued.extension_is_valuation :
 valuation.is_valuation (valued.extension : (hat K) → Γ₀ K) :=
{ map_zero := by exact_mod_cast valuation.map_zero _,
  map_one := by { rw [← completion.coe_one, valued.extension_extends (1 : K)], exact valuation.map_one _ },
  map_mul := λ x y, begin
    apply completion.induction_on₂ x y,
    { have c1 : continuous (λ (x : (hat K) × hat K), valued.extension (x.1 * x.2)),
        from valued.continuous_extension.comp (continuous_mul continuous_fst continuous_snd),

      have c2 : continuous (λ (x : (hat K) × hat K), valued.extension x.1 * valued.extension x.2),
        from continuous_mul (valued.continuous_extension.comp continuous_fst)
                            (valued.continuous_extension.comp continuous_snd),
      exact is_closed_eq c1 c2 },
    { intros x y,
      norm_cast,
      exact valuation.map_mul _ _ _ },
  end,
  map_add := λ x y, begin
    apply completion.induction_on₂ x y,
    { exact is_closed_union
        (is_closed_le ((valued.continuous_extension).comp continuous_add')
        ((valued.continuous_extension).comp continuous_fst))
        (is_closed_le ((valued.continuous_extension).comp continuous_add')
        ((valued.continuous_extension).comp continuous_snd)) },
    { intros x y,
      norm_cast,
      exact valuation.map_add _ _ _ },
  end }
end valuation_on_valued_field_completion
