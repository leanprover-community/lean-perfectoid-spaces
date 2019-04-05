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

open set valuation

namespace linear_ordered_comm_group
variables {α : Type*} [linear_ordered_comm_group α]
instance inhabited : inhabited α := ⟨1⟩

lemma mul_lt_right  :
  ∀ {a b} c : α, a < b → a*c < b*c :=
begin
  introv h,
  rw lt_iff_le_and_ne,
  refine ⟨linear_ordered_comm_group.mul_le_mul_right (le_of_lt h) _, _⟩,
  intro h',
  rw mul_right_cancel  h' at h,
  exact lt_irrefl b h
end

lemma lt_of_mul_lt_mul_left {α : Type*} [linear_ordered_comm_group α] :
  ∀ a b c : α, a * b < a * c → b < c :=
λ a b c h, lt_of_not_ge (λ h', lt_irrefl _ $ lt_of_lt_of_le h $
                               linear_ordered_comm_group.mul_le_mul_left h' a)
end linear_ordered_comm_group

section
set_option old_structure_cmd true

/-- An ordered commutative monoid is a commutative monoid
  with a partial order such that addition is an order embedding, i.e.
  `a * b ≤ a * c ↔ b ≤ c`. These monoids are automatically cancellative. -/
class actual_ordered_comm_monoid (α : Type*) extends comm_monoid α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c)
end

lemma actual_ordered_comm_monoid.mul_lt_mul {α : Type*} [actual_ordered_comm_monoid α]
{a b c d : α} : a < b → c < d → a*c < b*d :=
sorry

variables {Γ : Type*} [linear_ordered_comm_group Γ]

lemma with_zero.not_lt_zero : ∀ (x : with_zero Γ), x < 0 → false :=
begin
  intros x h,
  induction x using with_zero.cases_on,
  { exact lt_irrefl 0 h },
  { exact (with_zero.not_some_le_zero : ¬ (x : with_zero Γ) ≤ 0) (le_of_lt h) },
end

lemma with_zero.some_lt_some : ∀ (x y : Γ), (x : with_zero Γ) < y ↔ x < y :=
begin
  intros x y,
  sorry
end


open with_zero

instance : actual_ordered_comm_monoid (with_zero Γ) :=
{ mul_le_mul_left := λ x y x_le_y z,
    begin
      induction z using with_zero.cases_on,
      { simp },
      { induction x using with_zero.cases_on,
        { simp },
        { rw mul_coe,
          induction y using with_zero.cases_on ; simp at x_le_y,
          { exact false.elim x_le_y },
          { rw mul_coe,
            simp,
            exact linear_ordered_comm_group.mul_le_mul_left x_le_y z } } }
    end,
  lt_of_mul_lt_mul_left := λ x y z hlt,
    begin
      induction z using with_zero.cases_on,
      { rw mul_zero at hlt,
        exact false.elim (with_zero.not_lt_zero _ hlt) },
      { induction x using with_zero.cases_on;
        induction y using with_zero.cases_on ; simp at hlt ;
        try { exact false.elim (with_zero.not_lt_zero _ hlt) },
        { exact zero_lt_some },
        { rw some_lt_some at hlt ⊢,
          exact linear_ordered_comm_group.lt_of_mul_lt_mul_left x _ _ hlt } }
    end,
  ..(by apply_instance : comm_monoid (with_zero Γ)),
  ..(by apply_instance : partial_order (with_zero Γ)),
}

variables {R : Type*} [ring R] (v : valuation R Γ)

instance valuation.lt_is_add_subgroup (γ : Γ): is_add_subgroup {x | v x < γ} :=
{ zero_mem := by simp only [valuation.map_zero, mem_set_of_eq] ; apply with_zero.zero_lt_some,
  add_mem := λ x y x_in y_in, lt_of_le_of_lt (map_add_le_max v x y) (max_lt x_in y_in),
  neg_mem := λ x x_in, by rwa [mem_set_of_eq, map_neg] }


def valuation.topology {R : Type*} [ring R] (v : valuation R Γ) : topological_space R :=
begin
  apply topology_of_subgroups (λ γ : Γ, {k | v k < γ}),
  { intros γ₁ γ₂,
    use min γ₁ γ₂,
    simp only [set_of_subset_set_of, subset_inter_iff],
    split ; intros x x_lt ;  rw coe_min at x_lt,
    { apply lt_of_lt_of_le x_lt (min_le_left _ _) },
    { apply lt_of_lt_of_le x_lt (min_le_right _ _) } },
  { intros x γ,
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
      exact none_lt_some, } },
  { intros x γ,
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
      rwa [← mul_assoc, with_zero.mul_left_inv _ (coe_ne_zero), one_mul, inv_coe] } },
  { intro γ,
    simp [image_subset_iff],
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
      exact actual_ordered_comm_monoid.mul_lt_mul r_in s_in},
    { rw [not_lt] at h,
      replace h := some_le_some_of_le h,
      use 1,
      rintro x ⟨r, r_in, s, s_in, rfl⟩,
      refine lt_of_lt_of_le _ h,
      rw [valuation.map_mul, show (1: Γ) = 1*1, from (mul_one _).symm, ← mul_coe],
      exact actual_ordered_comm_monoid.mul_lt_mul r_in s_in}}
end
