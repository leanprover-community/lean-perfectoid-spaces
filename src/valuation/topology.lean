import for_mathlib.nonarchimedean.is_subgroups_basis
import for_mathlib.uniform_space.group_basis
import valuation.canonical

/-!
# The topology on a valued ring

In this file, we define the topology induced by a valuation on a ring.
-/

local attribute [instance] classical.prop_decidable
noncomputable theory

local attribute [instance, priority 0] classical.decidable_linear_order

open set valuation linear_ordered_structure

local notation `𝓝` x: 70 := nhds x

section
universe variables u u₀
variables {R : Type u} [comm_ring R]
variables {Γ₀ : Type u₀} [linear_ordered_comm_group_with_zero Γ₀]

/-- The subgroup of elements whose valuation is less than a certain unit.
See [Wedhorn, Prop. & Def. 5.39]-/
def valuation.subgroup (v : valuation R Γ₀) (γ : units (v.value_monoid)) : set R :=
{r : R | canonical_valuation v r < γ}

lemma valuation.lt_is_add_subgroup (v : valuation R Γ₀) (γ : units (v.value_monoid)) :
  is_add_subgroup {x | canonical_valuation v x < γ} :=
{ zero_mem := by { have h := group_with_zero.unit_ne_zero γ, contrapose! h, simpa using h },
  add_mem := λ x y x_in y_in, lt_of_le_of_lt (valuation.map_add _ x y) (max_lt x_in y_in),
  neg_mem := λ x x_in, by rwa [mem_set_of_eq, map_neg] }

-- is this an OK place to put this?
lemma valuation.le_is_add_subgroup (v : valuation R Γ₀) (γ : units (v.value_monoid)) :
  is_add_subgroup {x | canonical_valuation v x ≤ γ} :=
{ zero_mem := by simp,
  add_mem := λ x y x_in y_in, le_trans (valuation.map_add _ x y) (max_le x_in y_in),
  neg_mem := λ x x_in, by rwa [mem_set_of_eq, map_neg] }

end

local attribute [instance] valuation.lt_is_add_subgroup

universe u

/-- A valued ring is a ring that comes equipped with a distinguished valuation.-/
class valued (R : Type u) [ring R] :=
(Γ₀ : Type u)
[grp : linear_ordered_comm_group_with_zero Γ₀]
(v : valuation R Γ₀)

attribute [instance] valued.grp

open valued

namespace valued
variables {R : Type*} [comm_ring R] [valued R]

/-- The function underlying the valuation of a valued ring.-/
def value : R → (valued.Γ₀ R) := (valued.v R)

local notation `v` := valued.value

-- The following four lemmas are restatements that seem to be unfortunately needed

lemma map_zero : v (0 : R) = 0 :=
valuation.map_zero _

lemma map_one : v (1 : R) = 1 :=
valuation.map_one _

lemma map_mul (x y : R) : v (x*y) = v x * v y :=
valuation.map_mul _ _ _

lemma map_add (x y : R) : v (x+y) ≤ max (v x) (v y) :=
valuation.map_add _ _ _

/-- The basis of open subgroups for the topology on a valued ring.-/
def subgroups_basis : subgroups_basis R :=
{ sets := range (valued.v R).subgroup,
  ne_empty := ne_empty_of_mem (mem_range_self 1),
  directed := begin
    rintros _ _ ⟨γ₀, rfl⟩ ⟨γ₁, rfl⟩,
    rw exists_mem_range,
    use min γ₀ γ₁,
    simp only [set_of_subset_set_of, subset_inter_iff, valuation.subgroup],
    split ; intros x x_lt ;  rw coe_min at x_lt,
    { exact lt_of_lt_of_le x_lt (min_le_left _ _) },
    { exact lt_of_lt_of_le x_lt (min_le_right _ _) }
  end,
  sub_groups := by { rintros _ ⟨γ, rfl⟩, exact (valued.v R).lt_is_add_subgroup γ },
  h_mul := begin
    rintros _ ⟨γ, rfl⟩,
    rw set.exists_mem_range',
    cases linear_ordered_structure.exists_square_le γ with γ₀ h,
    use γ₀,
    rintro x ⟨r, r_in, s, s_in, rfl⟩,
    refine lt_of_lt_of_le _ h,
    rw valuation.map_mul,
    exact mul_lt_mul' r_in s_in
  end,
  h_left_mul := begin
    rintros x _ ⟨γ, rfl⟩,
    rw exists_mem_range',
    dsimp [valuation.subgroup],
    by_cases Hx : ∃ γx : units (value_monoid (valued.v R)), canonical_valuation (valued.v R) x = γx,
    { cases Hx with γx Hx,
      simp only [image_subset_iff, set_of_subset_set_of, preimage_set_of_eq, valuation.map_mul],
      use γx⁻¹ * γ,
      intros y vy_lt,
      rw Hx,
      rw units.coe_mul at vy_lt,
      apply actual_ordered_comm_monoid.lt_of_mul_lt_mul_left (γx⁻¹ : value_monoid (valued.v R)),
      rwa [← mul_assoc, inv_mul_cancel' _ (group_with_zero.unit_ne_zero _), one_mul,
        ← group_with_zero.coe_inv_unit] },
    { rw [← ne_zero_iff_exists, not_not] at Hx,
      use 1,
      intros y y_in,
      rw [mem_set_of_eq, valuation.map_mul, Hx, zero_mul],
      exact zero_lt_unit _ }
  end,
  h_right_mul := begin
    rintros x _ ⟨γ, rfl⟩,
    rw exists_mem_range',
    dsimp [valuation.subgroup],
    by_cases Hx : ∃ γx : units (value_monoid (valued.v R)), canonical_valuation (valued.v R) x = γx,
    { cases Hx with γx Hx,
      simp only [image_subset_iff, set_of_subset_set_of, preimage_set_of_eq, valuation.map_mul],
      use γ * γx⁻¹,
      intros y vy_lt,
      rw Hx,
      apply actual_ordered_comm_monoid.lt_of_mul_lt_mul_right' (γx⁻¹ : value_monoid (valued.v R)),
      rwa [mul_assoc, mul_inv_cancel' _ (group_with_zero.unit_ne_zero _), mul_one,
        ← group_with_zero.coe_inv_unit], },
    { rw [← ne_zero_iff_exists, not_not] at Hx,
      use 1,
      intros y y_in,
      rw [mem_set_of_eq, valuation.map_mul, Hx, mul_zero],
      exact zero_lt_unit _ }
  end }

local attribute [instance] valued.subgroups_basis subgroups_basis.topology ring_filter_basis.topological_ring

lemma mem_basis_zero {s : set R} :
  s ∈ filter_basis.sets R ↔
  ∃ γ : units (value_monoid (valued.v R)), {x | canonical_valuation (valued.v R) x < γ} = s :=
iff.rfl


lemma mem_nhds {s : set R} {x : R} :
  (s ∈ 𝓝 x) ↔
  ∃ γ : units (value_monoid (valued.v R)), {y | canonical_valuation (valued.v R) (y - x) < γ } ⊆ s :=
begin
  erw [subgroups_basis.mem_nhds, exists_mem_range],
  exact iff.rfl,
end

lemma mem_nhds_zero {s : set R} :
  (s ∈ 𝓝 (0 : R)) ↔
  ∃ γ : units (value_monoid (valued.v R)), {x | canonical_valuation (valued.v R) x < γ } ⊆ s :=
by simp [valued.mem_nhds, sub_zero]

lemma loc_const {x : R} (h : canonical_valuation (valued.v R) x ≠ 0) :
  {y : R | canonical_valuation (valued.v R) y = canonical_valuation (valued.v R) x} ∈ 𝓝 x :=
begin
  rw valued.mem_nhds,
  rcases ne_zero_iff_exists.mp h with ⟨γ, hx⟩,
  use γ,
  rw ← hx,
  intros y y_in,
  exact valuation.map_eq_of_sub_lt _ y_in
end

/-- The uniform structure on a valued ring.-/
def uniform_space : uniform_space R :=
topological_add_group.to_uniform_space R

local attribute [instance] valued.uniform_space

/-- A valued ring is a uniform additive group.-/
lemma uniform_add_group : uniform_add_group R :=
topological_add_group_is_uniform

local attribute [instance] valued.uniform_add_group

lemma cauchy_iff {F : filter R} :
  cauchy F ↔ F ≠ ⊥ ∧ ∀ γ : units (value_monoid (valued.v R)), ∃ M ∈ F,
    ∀ x y, x ∈ M → y ∈ M → y - x ∈ {x : R | canonical_valuation (valued.v R) x < ↑γ} :=
begin
    rw add_group_filter_basis.cauchy_iff R rfl,
    apply and_congr iff.rfl,
    split,
    { intros h γ,
      apply h,
      erw valued.mem_basis_zero,
      use γ },
    { intros h U U_in,
      rcases valued.mem_basis_zero.mp U_in with ⟨γ, rfl⟩, clear U_in,
      apply h }
end
end valued
