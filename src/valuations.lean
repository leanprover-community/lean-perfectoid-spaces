import algebra.group_power
import set_theory.cardinal
import ring_theory.ideal_operations
import data.finsupp
import group_theory.quotient_group
import tactic.tidy
import for_mathlib.linear_ordered_comm_group
import ring_theory.localization
import tactic.abel
import for_mathlib.with_zero
import data.option.basic
import for_mathlib.finsupp_prod_inv
import for_mathlib.quotient_group
import ring_theory.subring

import tactic.where

local attribute [instance] classical.prop_decidable
noncomputable theory

universes u u₀ u₁ u₂ u₃ -- v is used for valuations

open function

variables {R : Type u₀}

namespace valuation
variables [comm_ring R]

-- Valuations on a commutative ring with values in {0} ∪ Γ
class is_valuation {Γ : Type u} [linear_ordered_comm_group Γ]
  (v : R → with_zero Γ) : Prop :=
(map_zero : v 0 = 0)
(map_one  : v 1 = 1)
(map_mul  : ∀ x y, v (x * y) = v x * v y)
(map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y)

end valuation

def valuation (R : Type u₀) [comm_ring R] (Γ : Type u) [linear_ordered_comm_group Γ] :=
{ v : R → with_zero Γ // valuation.is_valuation v }

namespace valuation
variables [comm_ring R]

-- A valuation is coerced to the underlying function R → {0} ∪ Γ
instance (R : Type u₀) [comm_ring R] (Γ : Type u) [linear_ordered_comm_group Γ] :
has_coe_to_fun (valuation R Γ) := { F := λ _, R → with_zero Γ, coe := subtype.val}

variables {Γ : Type u} [linear_ordered_comm_group Γ]
variables (v : valuation R Γ) {x y z : R}

instance : is_valuation v := v.property

@[simp] lemma map_zero : v 0 = 0 := v.property.map_zero
@[simp] lemma map_one  : v 1 = 1 := v.property.map_one
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := v.property.map_mul
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y := v.property.map_add

-- If x ∈ R is a unit then v x is non-zero
theorem map_unit (h : x * y = 1) : (v x).is_some :=
begin
  have h1 := v.map_mul x y,
  rw [h, map_one v] at h1,
  cases (v x),
  { exfalso,
    exact option.no_confusion h1 },
  { constructor }
end

-- We have just proven that (v x) is_some. Shouldn't we use option.get here?
definition unit_map : units R → Γ :=
λ u, match v u with
| some x := x
| none := 1
end

@[simp] theorem unit_map_eq (u : units R) : some (unit_map v u) = v u :=
begin
  unfold unit_map,
  have h1 := v.map_mul u.val u.inv,
  change _ = v u * _ at h1,
  rw [u.val_inv, v.map_one] at h1,
  cases h : (v u),
    rw h at h1,
    exfalso, exact option.no_confusion h1,
  refl,
end

lemma is_group_hom.unit_map : is_group_hom (unit_map v) :=
⟨λ a b, option.some.inj $
  show _ = (some _ * some _ : with_zero Γ),
  by simp⟩

@[simp] theorem map_neg_one : v (-1) = 1 :=
begin
  change v (-1 : units R) = 1,
  rw ← unit_map_eq,
  congr' 1,
  apply linear_ordered_comm_group.eq_one_of_pow_eq_one (_ : _ ^ 2 = _),
  rw pow_two,
  apply option.some.inj,
  change (some _ * some _ : with_zero Γ) = _,
  rw [unit_map_eq, ← v.map_mul, units.coe_neg, units.coe_one, neg_one_mul, neg_neg, v.map_one],
  refl
end

@[simp] lemma map_neg (x : R) : v (-x) = v x :=
calc v (-x) = v (-1 * x)   : by simp
        ... = v (-1) * v x : map_mul _ _ _
        ... = v x          : by simp

@[simp] theorem eq_zero_iff_le_zero {r : R} : v r = 0 ↔ v r ≤ v 0 :=
v.map_zero.symm ▸ with_zero.le_zero_iff_eq_zero.symm

section

variables {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]
variables {v₁ : R → with_zero Γ₁} {v₂ : R → with_zero Γ₂}
variables {ψ : Γ₁ → Γ₂}
variables (H12 : ∀ r, with_zero.map ψ (v₁ r) = v₂ r)
variables (Hle : ∀ g h : Γ₁, g ≤ h ↔ ψ g ≤ ψ h)
-- This include statement means that we have an underlying assumption
-- that ψ : Γ₁ → Γ₂ is order-preserving, and that v₁ and v₂ are functions with ψ ∘ v₁ = v₂.
include H12 Hle

theorem le_of_le (r s : R) : v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s :=
begin
  rw ←H12 r, rw ←H12 s,
  cases v₁ r; cases v₁ s; simp [Hle]
end

-- Restriction of a Γ₂-valued valuation to a subgroup Γ₁ is still a valuation
theorem valuation_of_valuation [is_group_hom ψ] (Hiψ : function.injective ψ) (H : is_valuation v₂) :
  is_valuation v₁ :=
{ map_zero := with_zero.map_inj Hiψ $
    by erw [H12, H.map_zero, ← with_zero.map_zero],
  map_one := with_zero.map_inj Hiψ $
    by erw [H12, H.map_one, with_zero.map_some, is_group_hom.one ψ]; refl,
  map_mul := λ r s, with_zero.map_inj Hiψ $
    by rw [H12, H.map_mul, ←H12 r, ←H12 s]; exact (with_zero.map_mul _ _ _).symm,
  map_add := λ r s,
  begin
    apply (is_valuation.map_add v₂ r s).imp _ _;
    erw [with_zero.map_le Hle, ←H12, ←H12];
    exact id
  end }

end

-- f : S → R induces map valuation R Γ → valuation S Γ
def comap {S : Type u₁} [comm_ring S] (f : S → R) [is_ring_hom f] : valuation S Γ :=
{ val := v ∘ f,
  property := by constructor;
    simp [is_ring_hom.map_zero f, is_ring_hom.map_one f, is_ring_hom.map_mul f, is_ring_hom.map_add f] }

section trivial
variables (S : ideal R) [prime : ideal.is_prime S]
include prime

-- trivial Γ-valued valuation associated to a prime ideal S
def trivial : valuation R Γ :=
{ val := λ x, if x ∈ S then 0 else 1,
  property :=
  { map_zero := if_pos S.zero_mem,
    map_one  := if_neg (assume h, prime.1 (S.eq_top_iff_one.2 h)),
    map_mul  := λ x y, begin
        split_ifs with hxy hx hy; try {simp}; exfalso,
        { cases ideal.is_prime.mem_or_mem prime hxy with h' h',
          { exact hx h' },
          { exact h h' } },
        { exact hxy (S.mul_mem_right h) },
        { exact hxy (S.mul_mem_right h) },
        { exact hxy (S.mul_mem_left h_1) }
      end,
    map_add  := λ x y, begin
        split_ifs with hxy hx hy; try {simp};
        try {left; exact le_refl _};
        try {right}; try {exact le_refl _},
        { have hxy' : x + y ∈ S := S.add_mem h h_1,
          exfalso, exact hxy hxy' }
      end } }

@[simp] lemma trivial_val :
(trivial S).val = (λ x, if x ∈ S then 0 else 1 : R → (with_zero Γ)) := rfl

end trivial

section supp
open with_zero

-- support of a valuation v : R → {0} ∪ Γ
def supp : ideal R :=
{ carrier := {x | v x = 0},
  zero := map_zero v,
  add  := λ x y hx hy, or.cases_on (map_add v x y)
    (λ hxy, le_antisymm (hx ▸ hxy) zero_le)
    (λ hxy, le_antisymm (hy ▸ hxy) zero_le),
  smul  := λ c x hx, calc v (c * x)
                        = v c * v x : map_mul v c x
                    ... = v c * 0 : congr_arg _ hx
                    ... = 0 : mul_zero _ }

@[simp] lemma mem_supp_iff (x : R) : x ∈ supp v ↔ v x = 0 := iff.rfl
@[simp] lemma mem_supp_iff' (x : R) : x ∈ (supp v : set R)↔ v x = 0 := iff.rfl

-- support is a prime ideal.
instance : ideal.is_prime (supp v) :=
⟨λ h, have h1 : (1:R) ∈ supp v, by rw h; trivial,
    have h2 : v 1 = 0 := h1,
    by rw [map_one v] at h2; exact option.no_confusion h2,
 λ x y hxy, begin
    dsimp [supp] at hxy ⊢,
    change v (x * y) = 0 at hxy,
    rw [map_mul v x y] at hxy,
    exact eq_zero_or_eq_zero_of_mul_eq_zero _ _ hxy
  end⟩

-- v(a)=v(a+s) if s in support. First an auxiliary lemma
lemma val_add_supp_aux (a s : R) (h : s ∈ supp v) : v (a + s) ≤ v a :=
begin
  cases map_add v a s with H H, exact H,
  change v s = 0 at h,
  rw h at H,
  exact le_trans H with_zero.zero_le
end

lemma val_add_supp (a s : R) (h : s ∈ supp v) : v (a + s) = v a :=
begin
  apply le_antisymm (val_add_supp_aux v a s h),
  convert val_add_supp_aux v (a + s) (-s) _, simp,
  rwa ideal.neg_mem_iff,
end

-- We have not yet extended a valuation v to a valuation on R/supp v
-- or its field of fractions.

-- "Extension" of a valuation v from R to R/supp(v).
-- Note: we could extend v from R to R/J where J is any
-- subset of supp(v).

-- First the function
definition on_quot_val {J : ideal R} (hJ : (J : set R) ⊆ supp v) :
  J.quotient → with_zero Γ :=
λ q, quotient.lift_on' q v $ λ a b h,
begin
  have hsupp : a - b ∈ supp v := hJ h,
  convert val_add_supp v b (a - b) hsupp,
  simp,
end

-- If Lean says "this is already in mathlib" then it's because my PR got accepted
-- and this decfinition can just be deleted.
definition quotient.ind₂' :
∀ {α : Sort*} {β : Sort*} {s₁ : setoid α} {s₂ : setoid β}
{p : quotient s₁ → quotient s₂ → Prop}
(h : ∀ (a₁ : α) (a₂ : β), p (quotient.mk' a₁) (quotient.mk' a₂))
(q₁ : quotient s₁) (q₂ : quotient s₂), p q₁ q₂
:= λ α β s₁ s₂ p h q₁ q₂, quotient.induction_on₂' q₁ q₂ h

-- Proof that function is a valuation.
variable {v}
instance on_quot_val.is_valuation {J : ideal R} (hJ : (J : set R) ⊆ supp v) :
is_valuation (on_quot_val v hJ) :=
{ map_zero := v.map_zero,
  map_one  := v.map_one,
  map_mul  := quotient.ind₂' $ v.map_mul,
  map_add  := quotient.ind₂' $ v.map_add }

-- Now the valuation
variable (v)
definition on_quot {J : ideal R} (hJ : (J : set R) ⊆ supp v) :
  valuation J.quotient Γ :=
{ val := v.on_quot_val hJ,
  property := on_quot_val.is_valuation hJ }

@[simp] lemma on_quot_comap_eq {J : ideal R} (hJ : (J : set R) ⊆ supp v) :
  (v.on_quot hJ).comap (ideal.quotient.mk J) = v :=
subtype.ext.mpr $ funext $
  λ r, @quotient.lift_on_beta _ _ (J.quotient_rel) v
  (λ a b h, have hsupp : a - b ∈ supp v := hJ h,
    by convert val_add_supp v b (a - b) hsupp; simp) _
-- The above proof is ugly.

-- quotient valuation on R/J has support supp(v)/J
-- NB : statement looks really unreadable
lemma supp_quot_supp {J : ideal R} (hJ : J ≤ supp v) :
supp (v.on_quot hJ) = (supp v).map (ideal.quotient.mk J) :=
begin
  apply le_antisymm,
  { rintro ⟨x⟩ hx,
    apply ideal.subset_span,
    exact ⟨x, hx, rfl⟩ },
  { rw ideal.map_le_iff_le_comap,
    intros x hx, exact hx }
end

end supp

end valuation

namespace valuation
open with_zero

section quotient_ring
variables [integral_domain R]
variables {Γ : Type u} [linear_ordered_comm_group Γ] (v : valuation R Γ)

open localization

-- Kenny says this should work for nonzero commrings
-- ne_zero_of_mem_non_zero_divisors uses integral domain though -- maybe it shouldn't
-- oh wait -- support is a prime ideal so if it's zero the ring is an ID anyway
/-- extension of valuation on ID with support 0 to field of fractions -/
definition on_frac_val (hv : supp v = 0) : quotient_ring R → with_zero Γ :=
quotient.lift (λ rs, v rs.1 / v rs.2.1 : R × non_zero_divisors R → with_zero Γ)
begin
  intros a b hab,
  rcases a with ⟨r,s,hs⟩,
  rcases b with ⟨t,u,hu⟩,
  rcases hab with ⟨w,hw,h⟩, classical,
  change v r / v s = v t / v u,
  replace hs := ne_zero_of_mem_non_zero_divisors hs,
  replace hu := ne_zero_of_mem_non_zero_divisors hu,
  replace hw := ne_zero_of_mem_non_zero_divisors hw,
  have hvs : v s ≠ 0 := λ H, hs ((submodule.mem_bot).mp (lattice.eq_bot_iff.1 hv H)),
  have hvu : v u ≠ 0 := λ H, hu ((submodule.mem_bot).mp (lattice.eq_bot_iff.1 hv H)),
  have hvw : v w ≠ 0 := λ H, hw ((submodule.mem_bot).mp (lattice.eq_bot_iff.1 hv H)),
  rw [with_zero.div_eq_div hvs hvu],
  rw [sub_mul, sub_eq_zero] at h, replace h := congr_arg v h,
  iterate 4 { rw map_mul at h },
  cases option.is_some_iff_exists.1 (is_some_iff_ne_none.2 hvw) with w hvw, rw hvw at h, rw mul_comm,
  cases v s * v t; cases v u * v r, { refl }, { simpa using h }, { simpa using h },
  congr' 1, replace h := option.some.inj h, symmetry, exact mul_right_cancel h
end

@[simp] lemma on_frac_val_mk (hv : supp v = 0) (rs : R × non_zero_divisors R) :
  v.on_frac_val hv (⟦rs⟧) = v rs.1 / v rs.2.1 := rfl

@[simp] lemma on_frac_val_mk' (hv : supp v = 0) (rs : R × non_zero_divisors R) :
  v.on_frac_val hv (quotient.mk' rs) = v rs.1 / v rs.2.1 := rfl

-- TODO Does this work yet?
-- example (R : Type*) [integral_domain R] : discrete_field (quotient_ring R) := by apply_instance
-- If it does, then mathlib fixed the problem and the next two lines can be removed
instance foobar (R : Type*) [integral_domain R] : discrete_field (quotient_ring R) :=
quotient_ring.field.of_integral_domain R

@[simp] lemma non_zero_divisors_one_val : (1 : non_zero_divisors R).val = 1 := rfl

def on_frac_val.is_valuation (hv : supp v = 0) : is_valuation (v.on_frac_val hv) :=
{ map_zero := show v.on_frac_val hv (quotient.mk' ⟨0,1⟩) = 0, by simp,
  map_one  := show v.on_frac_val hv (quotient.mk' ⟨_,1⟩) = 1, by simp,
  map_mul  := quotient.ind₂' $ λ x y,
  begin
    change v(x.1 * y.1) * (v((x.2 * y.2).val))⁻¹ =
      v(x.1) * (v(x.2.val))⁻¹ * (v(y.1) * (v(y.2.val))⁻¹),
    erw [v.map_mul, v.map_mul, with_zero.mul_inv_rev],
    simp [mul_assoc, mul_comm, mul_left_comm]
  end,
  map_add  := quotient.ind₂' $ λ x y,
  begin
    let x_plus_y : quotient_ring R :=
      ⟦⟨x.2 * y.1 + y.2 * x.1, _, is_submonoid.mul_mem x.2.2 y.2.2⟩⟧,
    change on_frac_val v hv x_plus_y ≤ _ * _ ∨ on_frac_val v hv x_plus_y ≤ _ * _,
    dsimp,
    cases (is_valuation.map_add v (x.2 * y.1) (y.2 * x.1)) with h h;
    [right, left];
    refine le_trans (linear_ordered_comm_monoid.mul_le_mul_right h _) _;
    erw [v.map_mul, v.map_mul, with_zero.mul_inv_rev];
    simp only [mul_assoc, mul_comm];
    apply with_zero.mul_le_mul_left;
    refine le_trans (le_of_eq _)
      (le_trans (linear_ordered_comm_monoid.mul_le_mul_right
        (mul_inv_self $ v (_ : R × (non_zero_divisors R)).snd.val) _) $
        le_of_eq $ one_mul _),
    exact x, rw mul_assoc, refl,
    exact y, conv { to_lhs, congr, skip, rw mul_comm }, rw mul_assoc, refl,
  end }

def on_frac (hv : supp v = 0) : valuation (quotient_ring R) Γ :=
{ val := on_frac_val v hv,
  property := on_frac_val.is_valuation v hv }

@[simp] lemma on_frac_comap_eq (hv : supp v = 0) :
  (v.on_frac hv).comap (of_comm_ring R (non_zero_divisors R)) = v :=
subtype.ext.mpr $ funext $ λ r, show v r / v 1 = v r, by simp

end quotient_ring

--section discrete_field

variables [comm_ring R]
variables {Γ : Type u} [linear_ordered_comm_group Γ] (v : valuation R Γ)

definition valuation_field_aux := (supp v).quotient

instance : integral_domain (valuation_field_aux v) := by delta valuation_field_aux; apply_instance

definition valuation_field := localization.quotient_ring (valuation_field_aux v)

instance : discrete_field (valuation_field v) := by delta valuation_field; apply_instance

section
open ideal

definition on_valuation_field : valuation (valuation_field v) Γ :=
on_frac (v.on_quot (set.subset.refl _))
begin
  rw [supp_quot_supp],
  -- from here it should be a 1-liner
  rw zero_eq_bot,
  apply lattice.eq_bot_iff.2,
  apply map_le_iff_le_comap.2,
  intros x hx,
  erw submodule.mem_bot,
  exact ideal.quotient.eq_zero_iff_mem.2 hx
end

end

definition valuation_ring := {x | v.on_valuation_field x ≤ 1}

instance : is_subring (valuation_ring v) :=
{ zero_mem := show v.on_valuation_field 0 ≤ 1, by simp,
  add_mem := λ x y hx hy,
  by cases (v.on_valuation_field.map_add x y) with h h;
    exact le_trans h (by assumption),
  neg_mem := by simp [valuation_ring],
  one_mem := by simp [valuation_ring, le_refl],
  mul_mem := λ x y (hx : _ ≤ _) (hy : _ ≤ _), show v.on_valuation_field _ ≤ 1,
  by convert le_trans (linear_ordered_comm_monoid.mul_le_mul_left hy _) _; simp [hx] }

#print lt_of_le_of_ne
-- theorem lt_of_le_of_ne : ∀ {α : Type u} [_inst_1 : partial_order α] {a b : α},
-- a ≤ b → a ≠ b → a < b := _
#print lt_of_le_of_ne'
-- theorem lt_of_le_of_ne' : ∀ {α : Type u} [_inst_1 : partial_order α] {a b : α},
-- a ≤ b → a ≠ b → a < b := _

definition max_ideal : ideal (valuation_ring v) :=
{ carrier := { r | v.on_valuation_field r < 1 },
  zero := show v.on_valuation_field 0 < 1, by apply lt_of_le_of_ne; simp,
  add := λ x y (hx : _ < 1) (hy : _ < 1),
  show v.on_valuation_field _ < 1,
    by cases (v.on_valuation_field.map_add x y) with h h;
      exact lt_of_le_of_lt h (by assumption),
  smul := λ c x (hx : _ < 1),
  show v.on_valuation_field _ < 1,
  begin
    refine lt_of_le_of_lt _ _,
    swap,
    convert (linear_ordered_comm_monoid.mul_le_mul_right _ _),
    exact map_mul _ _ _,
    swap,
    convert c.property,
    simpa using hx
  end }

instance max_ideal_is_maximal : (max_ideal v).is_maximal :=
begin
  rw ideal.is_maximal_iff,
  split,
  { show (1 : valuation_ring v) ∉ max_ideal v,
    exact λ (H : _ < _), ne_of_lt H (map_one _) },
  { show ∀ (J : ideal (valuation_ring v)) (x : valuation_ring v),
      max_ideal v ≤ J → x ∉ max_ideal v → x ∈ J → (1 : valuation_ring v) ∈ J,
    intros J x hJ hxni hxinJ,
    cases x with x hx,
    have vx : v.on_valuation_field x = 1 :=
    begin
      rw eq_iff_le_not_lt,
      split; assumption
    end,
    have xinv_mul_x : (x : valuation_field v)⁻¹ * x = 1 :=
    begin
      apply inv_mul_cancel,
      intro hxeq0,
      simpa [hxeq0] using vx
    end,
    have hxinv : v.on_valuation_field x⁻¹ ≤ 1 :=
    begin
      refine le_of_eq _,
      symmetry,
      simpa [xinv_mul_x, vx] using v.on_valuation_field.map_mul x⁻¹ x
    end,
    convert J.smul_mem ⟨x⁻¹, hxinv⟩ hxinJ,
    symmetry,
    apply subtype.val_injective,
    exact xinv_mul_x }
end

definition residue_field := (max_ideal v).quotient

-- this should be a discrete field, I think
instance : field (residue_field v) := ideal.quotient.field _

-- The value group of v is the smallest subgroup Γ_v of Γ for which v takes
-- values in {0} ∪ Γ_v
definition value_group := group.closure {a : Γ | ∃ r : R, v r = some a}

definition value_group_v (v : R → with_zero Γ) [is_valuation v] :=
group.closure ({a : Γ | ∃ r : R, v r = some a})

instance : group (value_group v) :=
@subtype.group _ _ (value_group v) (group.closure.is_subgroup {a : Γ | ∃ r : R, v r = some a})

instance valuation.group_v (v : R → with_zero Γ) [is_valuation v] : group (value_group_v v) :=
  @subtype.group _ _ (value_group_v v) (group.closure.is_subgroup {a : Γ | ∃ r : R, v r = some a})

end valuation

namespace valuation
open quotient_group

variables [comm_ring R] [decidable_eq R]

-- This structure is scary because it has a random Γ : Type u₀ inside, but
-- we don't use it very often; it's an intermediate thing.
structure minimal_valuation.parametrized_subgroup (Γ' : Type u) [linear_ordered_comm_group Γ'] :=
(Γ : Type u₀)
[grp : comm_group Γ]
(inc : Γ → Γ')
[hom : is_group_hom inc]
(inj : function.injective inc)

local attribute [instance] parametrized_subgroup.grp
local attribute [instance] parametrized_subgroup.hom

variables {Γ : Type u} [linear_ordered_comm_group Γ]
variables (v : valuation R Γ)

include R v

-- Why do we need this?
set_option class.instance_max_depth 41

def of_free_group_aux (r : R) : Γ := option.get_or_else (v r) 1

def of_free_group : multiplicative (R →₀ ℤ) → Γ :=
λ f, finsupp.prod f (λ r n, (of_free_group_aux v r) ^ n)

instance : is_group_hom (of_free_group v) :=
⟨λ f₁ f₂, finsupp.prod_add_index (λ _, rfl) $ λ _ _ _, gpow_add _ _ _⟩

-- This definition helps resolve the set-theoretic issues caused by the
-- fact that the adic spectrum of R is all equivalence classes of
-- valuations, where the value group can vary arbitrarily. It shows
-- that if v : R → {0} ∪ Γ and if R has type Type u₀ then v is equivalent
-- to a valuation taking values in {0} ∪ Γ₀ with Γ₀ also of type u₀.
def minimal_value_group : minimal_valuation.parametrized_subgroup Γ :=
{ Γ     := quotient (is_group_hom.ker (of_free_group v)),
  inc   := inc (of_free_group v),
  hom   := by apply_instance,
  inj   := inc_injective (of_free_group v) }

namespace minimal_value_group

-- This function eats an arbitrary valuation and returns an auxiliary
-- function from R to the minimal value group, a group in the same universe as R.
-- Note that it is not a valuation, as the value 0 is not allowed; stuff in the
-- support of v gets sent to 1 not 0. This is an auxiliary function which
-- we probably won't be using outside this file if we get the API right.
def mk (r : R) : (minimal_value_group v).Γ :=
quotient_group.mk (finsupp.single r (1 : ℤ))

-- the auxiliary function agrees with v away from the support.
lemma mk_some {r : R} {g : Γ} (h : v r = some g) :
  v r = some ((minimal_value_group v).inc (mk v r)) :=
begin
  rw h,
  congr' 1,
  dsimp [inc, minimal_value_group, minimal_value_group.mk, of_free_group, of_free_group_aux],
  erw finsupp.prod_single_index; finish
end

-- the minimal value group is isomorphic to a subgroup of Γ so inherits an order.
instance : linear_ordered_comm_group (minimal_value_group v).Γ :=
begin
  cases minimal_value_group v with Γ₀ _ ψ _ inj,

  letI Γ₁linord : linear_order Γ₀ :=
  { le := λ g h, ψ g ≤ ψ h,
    le_refl := λ _, le_refl _,
    le_trans := λ _ _ _ hab hbc, le_trans hab hbc,
    le_antisymm := λ g h Hgh Hhg, inj $ le_antisymm Hgh Hhg,
    le_total := λ g h, le_total _ _ },
  exact ⟨λ a b H c,
    begin
      change ψ (c * a) ≤ ψ (c * b),
      rw [is_group_hom.mul ψ c b, is_group_hom.mul ψ c a],
      exact linear_ordered_comm_group.mul_le_mul_left H _,
    end⟩
end

end minimal_value_group

-- This is function taking a valuation v to a u₁-universe-valued valuation equivalent to it.
-- This is the final resolution of the set-theoretic issues caused by quantifying
-- over all value groups. This function is also correct on the support.
definition minimal_valuation.val (r : R) : with_zero ((minimal_value_group v).Γ) :=
match v r with
| some _ := some (minimal_value_group.mk v r)
| 0 := 0
end

namespace minimal_valuation

@[simp] lemma zero {r} (h : v r = 0) : val v r = 0 :=
by simp [val, h]

lemma some {r} {g} (h : v r = some g) : val v r = some (minimal_value_group.mk v r) :=
by simp [val, h]

lemma map (r : R) :
with_zero.map (minimal_value_group v).inc (val v r) = v r :=
begin
  destruct (v r),
  { intro h, change v r = 0 at h,
    simp [zero v h, h], },
  { intros g h,
    rw [minimal_value_group.mk_some v h, some v h, with_zero.map_some] },
end

end minimal_valuation

-- the map from valuations to minimal valuations
def minimal_valuation : valuation R (minimal_value_group v).Γ :=
{ val := minimal_valuation.val v,
  property := let Γ₁ := minimal_value_group v in
    valuation_of_valuation (minimal_valuation.map v) (λ g h, iff.refl _) Γ₁.inj (v.property) }

end valuation

namespace valuation
variables [comm_ring R]
variables {Γ : Type u}   [linear_ordered_comm_group Γ]
variables {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]
variables {Γ₃ : Type u₃} [linear_ordered_comm_group Γ₃]

-- Definition of equivalence relation on valuations
def is_equiv (v₁ : valuation R Γ₁) (v₂ : valuation R Γ₂) : Prop :=
∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s

-- Theorem that valuation v is equivalent to the associated minimal valuation.
lemma minimal_valuation_is_equiv (v : valuation R Γ) :
  v.minimal_valuation.is_equiv v :=
le_of_le (minimal_valuation.map v) (λ g h, iff.refl _)

namespace is_equiv
variables {v : valuation R Γ} {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} {v₃ : valuation R Γ₃}

@[refl] lemma refl : v.is_equiv v :=
λ _ _, iff.refl _

@[symm] lemma symm (h : v₁.is_equiv v₂) : v₂.is_equiv v₁ :=
λ _ _, iff.symm (h _ _)

@[trans] lemma trans (h₁₂ : v₁.is_equiv v₂) (h₂₃ : v₂.is_equiv v₃) : v₁.is_equiv v₃ :=
λ _ _, iff.trans (h₁₂ _ _) (h₂₃ _ _)

lemma of_eq {v' : valuation R Γ} (h : v = v') : v.is_equiv v' :=
by subst h; refl

lemma comap {S : Type u₃} [comm_ring S] (f : S → R) [is_ring_hom f] (h : v₁.is_equiv v₂) :
  (v₁.comap f).is_equiv (v₂.comap f) :=
λ r s, h (f r) (f s)

lemma on_quot {J : ideal R} (hJ : (J : set R) ⊆ supp v) :
  is_equiv ((v.on_quot hJ).comap (ideal.quotient.mk J)) v :=
of_eq (on_quot_comap_eq _ _)

open localization

lemma on_frac {R : Type u₀} [integral_domain R] (v : valuation R Γ) (hv : supp v = 0) :
  is_equiv ((v.on_frac hv).comap (of_comm_ring R (non_zero_divisors R))) v :=
of_eq (on_frac_comap_eq v hv)

-- -- Wedhorm 1.27 iii -> ii prep
-- lemma supp_sub_of_is_equiv (h : is_equiv v₁ v₂) : ((supp v₁) : set R) ⊆ supp v₂ :=
-- λ r Hr, by rwa [mem_supp_iff', eq_zero_iff_le_zero, ←(h r 0), ←eq_zero_iff_le_zero, ←mem_supp_iff']

/-- Wedhorm 1.27 iii -> ii (part a) -/
lemma supp_eq (h : v₁.is_equiv v₂) : supp v₁ = supp v₂ :=
ideal.ext $ λ r,
calc r ∈ supp v₁ ↔ v₁ r = 0    : mem_supp_iff' _ _
             ... ↔ v₁ r ≤ v₁ 0 : eq_zero_iff_le_zero _
             ... ↔ v₂ r ≤ v₂ 0 : h r 0
             ... ↔ v₂ r = 0    : (eq_zero_iff_le_zero _).symm
             ... ↔ r ∈ supp v₂ : (mem_supp_iff' _ _).symm

open is_group_hom

def quot_of_quot_of_equiv (h : v₁.is_equiv v₂) : (supp v₁).quotient → (supp v₂).quotient :=
ideal.quotient.lift _ (ideal.quotient.mk _)
begin
  intros r hr,
  rwa [ideal.quotient.eq_zero_iff_mem, ←h.supp_eq]
end

instance (h : v₁.is_equiv v₂) : is_ring_hom (h.quot_of_quot_of_equiv) :=
by delta quot_of_quot_of_equiv; apply_instance

lemma quot_of_quot_of_equiv_inj (h : v₁.is_equiv v₂) : injective h.quot_of_quot_of_equiv :=
begin
  apply injective_of_has_left_inverse,
  use h.symm.quot_of_quot_of_equiv,
  rintro ⟨q⟩,
  delta quot_of_quot_of_equiv,
  erw ideal.quotient.lift_mk,
  refl
end

-- This should be moved elsewhere
def localization.r_iff {S : set R} [is_submonoid S] :
  ∀ x y, localization.r R S x y ↔ ∃ t ∈ S, (x.2.1 * y.1 - y.2.1 * x.1) * t = 0
| ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ := iff.rfl

-- This should be moved elsewhere
def frac_map {R : Type u₁} [integral_domain R] {S : Type u₂} [integral_domain S]
(f : R → S) [is_ring_hom f] (hf : injective f) :
  quotient_ring R → quotient_ring S :=
quotient.lift (λ rs : R × (non_zero_divisors R),
let mk : S → quotient_ring S := of_comm_ring _ _ in
(mk $ f rs.1) / (mk $ f rs.2.val))
begin
  intros x y hxy,
  dsimp,
  rw div_eq_div_iff,
  refine quotient.sound _,
  dsimp [(≈), setoid.r] at hxy ⊢,
  erw localization.r_iff at hxy ⊢,
  rcases hxy with ⟨t, ht, ht'⟩,
  use f t,
end

def frac_of_frac_of_equiv (h : v₁.is_equiv v₂) :
  valuation_field v₁ → valuation_field v₂ :=
frac_map h.quot_of_quot_of_equiv h.quot_of_quot_of_equiv_inj


-- lemma ker_eq_ker_of_equiv (h : v₁.is_equiv v₂) :
--   ker (of_free_group v₁) = ker (of_free_group v₂) :=
-- begin
--   ext f,
--   split; rw [mem_ker, mem_ker]; intro hf,
-- end

end is_equiv

section
variables {v : valuation R Γ} {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} {v₃ : valuation R Γ₃}

open is_group_hom quotient_group function

-- Notes: if v1 equiv v2 then we need a bijection from the image of v1 to the
-- image of v2; we need that the supports are the same; we need that
-- the minimal_value_group for v2 is isomorphic to the subgroup of Gamma_2 generated
-- by the image of the stuff not in the support.
-- More notes: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/eq.2Erec.20goal

-- Theorem we almost surely need -- two equivalence valuations have isomorphic
-- value groups. But we're not ready for it yet.

#check is_group_hom.mem_ker
set_option pp.proofs true

-- set_option trace.class_instances true

set_option class.instance_max_depth 50
-- Idea: prove Wedhorn 1.27.
def minimal_valuations_biject_of_equiv (v₁ : valuation R Γ₁) (v₂ : valuation R Γ₂) (h : is_equiv v₁ v₂) :
  (minimal_value_group v₁).Γ → (minimal_value_group v₂).Γ :=
@quotient_group.map _ _ _ _ _ _ _ _ id is_group_hom.id _

end
-- λ g, quotient.lift_on' g (λ g, finsupp.prod g (λ r n, (minimal_value_group.mk v₂ r) ^ n)) $
-- λ g₁ g₂ h12,
-- begin
--   change finsupp.prod _ _ = finsupp.prod _ _,
--   change _ ∈ _ at h12,
--   rw is_group_hom.mem_ker at h12,
--   change finsupp.prod (-_ + _) _ = _ at h12,
--   rw [finsupp.prod_add_index, finsupp.prod_neg_index', mul_eq_one_iff_eq_inv, inv_inj'] at h12,
--   iterate 5 { sorry },
--  cases h12 with h12 hoops,
--    swap,cases hoops,
/-  induction g with g g₁ g₂ h12,
    exact finsupp.prod g (λ r n,(minimal_value_group.mk v₂ r) ^ n),
  cases h12 with h12 hoops,
    swap,cases hoops,
  -- If φ1 is the function from R to Γ1 which is v1 away from the support and
  -- sends the support to 1, then φ1 extends to a group hom Z[R] -> Γ1 (free ab group on R)
  -- and h12 is the hypothesis that g₁⁻¹g₂ is in the kernel, so g₁ and g₂ get sent to
  -- the same element of Γ1. We need the analogous result for φ2.
  convert rfl,
  suffices : finsupp.prod g₁ (λ (r : R) (n : ℤ), minimal_value_group.mk v₂ r ^ n) =
             finsupp.prod g₂ (λ (r : R) (n : ℤ), minimal_value_group.mk v₂ r ^ n),
   rw this,
    swap,sorry,
  generalize : quot.sound _ = h1,-/
-- end

end valuation

/- quotes from zulip (mostly Mario) (all 2018)

https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Perfectoid.20spaces/near/129009961

class is_valuation {α : Type*} [linear_ordered_comm_group α]
  {R : Type*} [comm_ring R] (f : R → option α) : Prop :=
(map_zero : f 0 = 0)
(map_one  : f 1 = 1)
(map_mul  : ∀ x y, f (x * y) = f x * f y)
(map_add  : ∀ x y, f (x + y) ≤ f x ∨ f (x + y) ≤ f y)

namespace is_valuation

...

structure valuation (R : Type*) [comm_ring R] (α : Type*) [Hα : linear_ordered_comm_group α] :=
(f : R → option α)
(Hf : is_valuation f)

...

**All 03 Jul 2018** Mario + comments from me

MC: What's wrong, again, with defining Spv as the collection of all valuation relations?
KB: All proofs need an actual valuation
MC: You can define your own version of quot.lift and quot.mk that take valuations
MC: valuation functions that is
[quot.lift is the statement that if I have a function on valuations which is constant
on equiv classes then I can produce a function on Spv]
MC: You only use the relations as inhabitants of the type so that the universe isn't pushed up,
    but all the work uses functions
MC: You will need to prove the computation rule, so it won't be definitional, but otherwise it
    should work smoothly if your API is solid
MC: No equivalence class needed either
MC: quot.mk takes a valuation function and produces an element of Spv
MC: quot.lift takes a function defined on valuation functions and produces a function defined on Spv
KB: So what about proofs which go "Spv(R) is compact. Proof: take an element of Spv(R), call it v or
    f or whatever, and now manipulate f in the following way..."
MC: That's quot.lift
MC: Actually you will want quot.ind as well
["any subset of the quotient type containing the image of quot.mk is everything"]
or equivalently quot.exists_rep
[lemma exists_rep {α : Sort u} {r : α → α → Prop} (q : quot r) : ∃ a : α, (quot.mk r a) = q :=
]
MC: that is, for every element of Spv there is a valuation function that quot.mk's to it
MC: Note it's not actually a function producing valuation functions, it's an exists
MC: if you prove analogues of those theorems for your type, then you have constructed the
    quotient up to isomorphism
MC: This all has a category theoretic interpretation as a coequalizer, and all constructions
    are natural in that category
MC: As opposed to, say, quot.out, which picks an element from an equivalence class
MC: Although in your case if I understand correctly you also have a canonical way to define quot.out
    satisfying some other universal property to do with the ordered group
    where the valuation and ring have to share the same universe.
    You can prove that the universe need not be the same as part of the universal properties
    i.e. Spv.mk takes as input a valuation function  (v : valuation R A) where {R : Type u} and
    {A : Type v} (so it isn't just instantiating the exists)
KB: "If you want to be polymorphic" -- I just want to do maths. I have no idea if I want to be polymorphic.
     If I just want to define a perfectoid space, do I want to be polymorphic?
MC : In lean, you should usually be polymorphic
     at least in contravariant positions (i.e. the inputs should be maximally polymorphic, the output should
      be minimally polymorphic)
     This is why we don't have nat : Type u
     The general rule is to keep types out of classes if at all possible. Lean behaves better when the
     types are given as "alpha" rather than "the type inside v", particularly if you start manipulating
     the functions (adding them, say).
     It is the same things that make the difference between bundled vs unbundled groups. When
     working "internally", i.e. calculations using the monoid structure, it is better for the type
     to be exposed as a variable
-/
