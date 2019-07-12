/-
In this file, we define the topology induced by a valuation on a ring

valuation.topology {Γ : Type*} [linear_ordered_comm_group Γ] {R : Type*} [ring R] :
    valuation R Γ → topological_space R
-/
import for_mathlib.nonarchimedean.is_subgroups_basis
import valuation.canonical -- we need the canonical valuation for the instance at the end

local attribute [instance] classical.prop_decidable
noncomputable theory

local attribute [instance, priority 0] classical.decidable_linear_order

open set valuation with_zero

variables {Γ : Type*} [linear_ordered_comm_group Γ]
variables {R : Type*} [ring R] (v : valuation R Γ)

lemma valuation.lt_is_add_subgroup (γ : Γ): is_add_subgroup {x | v x < γ} :=
{ zero_mem := by simp only [valuation.map_zero, mem_set_of_eq] ; apply with_zero.zero_lt_coe,
  add_mem := λ x y x_in y_in, lt_of_le_of_lt (map_add_le_max v x y) (max_lt x_in y_in),
  neg_mem := λ x x_in, by rwa [mem_set_of_eq, map_neg] }

-- is this an OK place to put this?
lemma valuation.le_is_add_subgroup (γ : Γ): is_add_subgroup {x | v x ≤ γ} :=
{ zero_mem := by simp only [valuation.map_zero, mem_set_of_eq]; apply le_of_lt (with_zero.zero_lt_coe),
  add_mem := λ x y x_in y_in, le_trans (map_add_le_max v x y) (max_le x_in y_in),
  neg_mem := λ x x_in, by rwa [mem_set_of_eq, map_neg] }

local attribute [instance] valuation.lt_is_add_subgroup

lemma valuation.subgroups_basis : is_subgroups_basis (λ γ : Γ, {x | v x < γ}) :=
{ sub_groups := valuation.lt_is_add_subgroup v,
  h_directed :=
    begin
      intros γ₁ γ₂,
      use min γ₁ γ₂,
      simp only [set_of_subset_set_of, subset_inter_iff],
      split ; intros x x_lt ;  rw coe_min at x_lt,
      { apply lt_of_lt_of_le x_lt (min_le_left _ _) },
      { apply lt_of_lt_of_le x_lt (min_le_right _ _) }
    end,
  h_left_mul :=
    begin
      intros x γ,
      by_cases Hx : ∃ γ : Γ, v x = γ,
      { cases Hx with γx Hx,
        simp only [Hx, image_subset_iff, set_of_subset_set_of, preimage_set_of_eq, valuation.map_mul],
        use γx⁻¹*γ,
        intros y vy_lt,
        rw ← with_zero.mul_coe at vy_lt,
        apply actual_ordered_comm_monoid.lt_of_mul_lt_mul_left (γx⁻¹ : with_zero Γ),
        rwa [← mul_assoc, with_zero.mul_left_inv _ (coe_ne_zero), one_mul, inv_coe] },
      { rw [← ne_zero_iff_exists, not_not] at Hx,
        use 1,
        intros y y_in,
        rcases (mem_image _ _ _).1 y_in with ⟨t, t_in, xty⟩,
        simp [xty.symm, Hx] }
    end,
  h_right_mul :=
    begin
      intros x γ,
      simp [image_subset_iff],
      induction v x using with_zero.cases_on,
      { simp },
      { use a⁻¹*γ,
        intros y vy_lt,
        rw mul_comm,
        rw ← with_zero.mul_coe at vy_lt,
        apply actual_ordered_comm_monoid.lt_of_mul_lt_mul_left (a⁻¹ : with_zero Γ),
        rwa [← mul_assoc, with_zero.mul_left_inv _ (coe_ne_zero), one_mul, inv_coe] }
    end,
  h_mul :=
    begin
      intro γ,
      by_cases h : γ < 1,
      { have : (γ*γ : with_zero Γ) < γ,
        { norm_cast,
          have := linear_ordered_structure.mul_lt_right γ h,
          rwa one_mul at this },
        use γ,
        rintro x ⟨r, r_in, s, s_in, rfl⟩,
        refine lt_trans _ this,
        rw valuation.map_mul,
        exact with_zero.mul_lt_mul r_in s_in},
      { rw [not_lt] at h,
        rw ← coe_le_coe at h,
        use 1,
        rintro x ⟨r, r_in, s, s_in, rfl⟩,
        refine lt_of_lt_of_le _ h,
        rw [valuation.map_mul, show (1: Γ) = 1*1, from (mul_one _).symm, ← mul_coe],
        exact with_zero.mul_lt_mul r_in s_in}
    end }

local attribute [instance] valuation.subgroups_basis

def valuation.ring_with_zero_nhd {R : Type*} [ring R] (v : valuation R Γ) : ring_with_zero_nhd R :=
is_subgroups_basis.to_ring_with_zero_nhd (λ γ : Γ, {x | v x < γ})

-- No harm making this an instance because this is the only correct instance on
-- the valuation field. Note: I use the canonical valuation not the induced valuation;
-- Patrick did *not* assume Γ was the value group above so his topology is not
-- constant across equivalence classes; this does not matter, but when making the
-- instance we need to choose the correct one, which is the canonical valuation.
noncomputable instance valuation_field.ring_with_zero_nhd
  {R : Type*} [comm_ring R] (v : valuation R Γ) :
ring_with_zero_nhd (valuation_field v) :=
valuation.ring_with_zero_nhd (valuation_field.canonical_valuation v)

noncomputable instance valuation_field.topology
  {R : Type*} [comm_ring R] (v : valuation R Γ) :
topological_space (valuation_field v) := ring_with_zero_nhd.topological_space _

noncomputable instance valuation_field.top_ring
  {R : Type*} [comm_ring R] (v : valuation R Γ) :
topological_ring (valuation_field v) := ring_with_zero_nhd.is_topological_ring _
