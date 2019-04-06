/-
In this file, we define the topology induced by a valuation on a ring

valuation.topology {Γ : Type*} [linear_ordered_comm_group Γ] {R : Type*} [ring R] :
    valuation R Γ → topological_space R
-/
import for_mathlib.nonarchimedean.basic
import valuation.basic

local attribute [instance] classical.prop_decidable
noncomputable theory

local attribute [instance, priority 0] classical.decidable_linear_order

open set valuation with_zero

variables {Γ : Type*} [linear_ordered_comm_group Γ]
variables {R : Type*} [ring R] (v : valuation R Γ)

instance valuation.lt_is_add_subgroup (γ : Γ): is_add_subgroup {x | v x < γ} :=
{ zero_mem := by simp only [valuation.map_zero, mem_set_of_eq] ; apply with_zero.zero_lt_some,
  add_mem := λ x y x_in y_in, lt_of_le_of_lt (map_add_le_max v x y) (max_lt x_in y_in),
  neg_mem := λ x x_in, by rwa [mem_set_of_eq, map_neg] }


def valuation.ring_with_zero_nhd {R : Type*} [ring R] (v : valuation R Γ) : ring_with_zero_nhd R :=
of_subgroups (λ γ : Γ, {k | v k < γ})
  (begin intros γ₁ γ₂,
    use min γ₁ γ₂,
    simp only [set_of_subset_set_of, subset_inter_iff],
    split ; intros x x_lt ;  rw coe_min at x_lt,
    { apply lt_of_lt_of_le x_lt (min_le_left _ _) },
    { apply lt_of_lt_of_le x_lt (min_le_right _ _) } end)
  (begin intros x γ,
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
      rw ← xty,
      simp [Hx],
      exact none_lt_some, } end)
  (begin intros x γ,
    simp [image_subset_iff],
    induction v x using with_zero.cases_on,
    { simp,
      use 1,
      intros _ _,
      exact zero_lt_some },
    { use a⁻¹*γ,
      intros y vy_lt,
      rw mul_comm,
      rw ← with_zero.mul_coe at vy_lt,
      apply actual_ordered_comm_monoid.lt_of_mul_lt_mul_left (a⁻¹ : with_zero Γ),
      rwa [← mul_assoc, with_zero.mul_left_inv _ (coe_ne_zero), one_mul, inv_coe] } end)
  (begin
    intro γ,
    by_cases h : γ < 1,
    { have : (γ*γ : with_zero Γ) < γ,
      { rw mul_coe,
        rw some_lt_some,
        have := linear_ordered_comm_group.mul_lt_right γ h,
        rwa one_mul at this },
      use γ,
      rintro x ⟨r, r_in, s, s_in, rfl⟩,
      refine lt_trans _ this,
      rw valuation.map_mul,
      exact with_zero.mul_lt_mul r_in s_in},
    { rw [not_lt] at h,
      replace h := some_le_some_of_le h,
      use 1,
      rintro x ⟨r, r_in, s, s_in, rfl⟩,
      refine lt_of_lt_of_le _ h,
      rw [valuation.map_mul, show (1: Γ) = 1*1, from (mul_one _).symm, ← mul_coe],
      exact with_zero.mul_lt_mul r_in s_in} end)
