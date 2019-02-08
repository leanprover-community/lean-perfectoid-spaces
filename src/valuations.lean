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

local attribute [instance, priority 0] classical.prop_decidable
noncomputable theory

universes u₁ u₂ u₃ -- v is used for valuations

namespace valuation

-- Valuations on a commutative ring with values in {0} ∪ Γ
class is_valuation {R : Type u₁} [comm_ring R] {Γ : Type u₂} [linear_ordered_comm_group Γ]
  (v : R → with_zero Γ) : Prop :=
(map_zero : v 0 = 0)
(map_one  : v 1 = 1)
(map_mul  : ∀ x y, v (x * y) = v x * v y)
(map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y)

end valuation

def valuation (R : Type u₁) [comm_ring R] (Γ : Type u₂) [linear_ordered_comm_group Γ] :=
{ v : R → with_zero Γ // valuation.is_valuation v }

namespace valuation

-- A valuation is coerced to the underlying function R → {0} ∪ Γ
instance (R : Type u₁) [comm_ring R] (Γ : Type u₂) [linear_ordered_comm_group Γ] :
has_coe_to_fun (valuation R Γ) := { F := λ _, R → with_zero Γ, coe := subtype.val}

variables {R : Type u₁} [comm_ring R]
variables {Γ : Type u₂} [linear_ordered_comm_group Γ]
variables (v : valuation R Γ) {x y z : R}

instance : is_valuation v := v.property

@[simp] lemma map_zero : v 0 = 0 := v.property.map_zero
@[simp] lemma map_one  : v 1 = 1 := v.property.map_one
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := v.property.map_mul
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y := v.property.map_add

-- If x ∈ R is a unit then v x is non-zero
theorem map_unit (h : x * y = 1) : option.is_some (v x) :=
begin
  have h1 := v.map_mul x y,
  rw [h, map_one v] at h1,
  cases (v x),
  { exfalso,
    exact option.no_confusion h1 },
  { constructor }
end

definition unit_map : units R → Γ :=
λ u, match v u with
| some x := x
| none := 1
end

theorem unit_map_eq (u : units R) : some (unit_map v u) = v u :=
begin
  unfold unit_map,
  have h1 := v.map_mul u.1 u.2,
  change _ = v u * _ at h1,
  rw [u.3, map_one v] at h1,
  cases h : (v u),
    rw h at h1,
    exfalso, exact option.no_confusion h1,
  refl,
end

lemma is_group_hom.unit_map : is_group_hom (unit_map v) :=
⟨λ a b, begin
  apply option.some.inj, change _ = (some _ * some _ : with_zero Γ),
  rw [unit_map_eq, unit_map_eq, unit_map_eq, units.coe_mul, v.map_mul]
end⟩

theorem map_neg_one : v (-1) = 1 :=
begin
  change v (-1 : units R) = 1, rw ← unit_map_eq, congr' 1,
  apply linear_ordered_comm_group.eq_one_of_pow_eq_one, change _ ^ 2 = _,
  rw pow_two, apply option.some.inj, change (some _ * some _ : with_zero Γ) = _,
  rw [unit_map_eq, ← v.map_mul, units.coe_neg, units.coe_one, neg_one_mul, neg_neg, v.map_one], refl
end

@[simp] theorem eq_zero_iff_le_zero {r : R} : v r = 0 ↔ v r ≤ v 0 :=
v.map_zero.symm ▸ with_zero.le_zero_iff_eq_zero.symm

section

variables {Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂]
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
  cases hr : (v₁ r) with g; cases hs : (v₁ s) with h; try {simp},
  { intro oops, exact option.no_confusion oops },
  { exact Hle g h }
end

-- Restriction of a Γ₂-valued valuation to a subgroup Γ₁ is still a valuation
theorem valuation_of_valuation [is_group_hom ψ]
  (Hiψ : function.injective ψ)
  (H : is_valuation v₂) :
is_valuation v₁ :=
{ map_zero := begin
    show v₁ 0 = 0,
    have H0 : v₂ 0 = 0 := H.map_zero,
    rw ←H12 0 at H0,
    change with_zero.map ψ (v₁ 0) = 0 at H0,
    cases h : v₁ 0, refl,
    exfalso,
    rw h at H0,
    revert H0,
    exact dec_trivial
  end,
map_one := begin
    show v₁ 1 = 1,
    have H0 : v₂ 1 = 1 := H.map_one,
    rw ←H12 1 at H0,
    cases h : v₁ 1,
    { change v₁ 1 = 0 at h, rw h at H0,
      simpa only [with_zero.map_zero] using H0 },
    { rw h at H0,
      change some (ψ val) = some 1 at H0,
      congr,
      apply Hiψ,
      rw [option.some_inj.1 H0, is_group_hom.one ψ] }
  end,
map_mul := begin
    intros r s,
    apply with_zero.map_inj Hiψ,
    rw [H12 (r * s), H.map_mul, ←H12 r, ←H12 s],
    symmetry,
    exact with_zero.map_mul _ _ _,
  end,
map_add := begin
    intros r s,
    cases is_valuation.map_add v₂ r s,
    { left,
      rw [←H12 r, ←H12 (r+s)] at h,
      rwa with_zero.map_le Hle },
    { right,
      rw [←H12 s, ←H12 (r+s)] at h,
      rwa with_zero.map_le Hle }
  end }

end

-- f : S → R induces map valuation R Γ → valuation S Γ
def map {S : Type u₃} [comm_ring S] (f : S → R) [is_ring_hom f] : valuation S Γ :=
{ val := v ∘ f,
  property :=
  { map_zero := by simp [is_ring_hom.map_zero f],
    map_one  := by simp [is_ring_hom.map_one f],
    map_mul  := by simp [is_ring_hom.map_mul f],
    map_add  := by simp [is_ring_hom.map_add f] } }

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
        { have H : x * y ∈ S, exact S.mul_mem_right h,
          exact hxy H },
        { have H : x * y ∈ S, exact S.mul_mem_right h,
          exact hxy H },
        { have H : x * y ∈ S, exact S.mul_mem_left h_1,
          exact hxy H }
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
include v

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

omit v

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
  change v s = 0 at h,
  cases map_add v a s with H H, exact H,
  rw h at H,
  have : v (a + s) = 0 := by simp [H],
  simp [this]
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
definition extension_to_quot_v {Γ : Type*} [linear_ordered_comm_group Γ]
  {R : Type*} [comm_ring R] (v : valuation R Γ) {J : ideal R} (hJ : (J : set R) ⊆ supp v):
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
instance extension_to_quot_v.is_valuation {J : ideal R} (hJ : (J : set R) ⊆ supp v) :
is_valuation (extension_to_quot_v v hJ) :=
{ map_zero := map_zero v,
  map_one := map_one v,
  map_mul := quotient.ind₂' $ λ a b, map_mul _ _ _,
  map_add := quotient.ind₂' $ λ a b, map_add _ _ _
  }

-- Now the valuation
definition extension_to_quot {Γ : Type*} [linear_ordered_comm_group Γ]
  {R : Type*} [comm_ring R] (v : valuation R Γ) {J : ideal R} (hJ : (J : set R) ⊆ supp v):
valuation J.quotient Γ := ⟨extension_to_quot_v v hJ,extension_to_quot_v.is_valuation hJ⟩


-- quotient valuation on R/J has support supp(v)/J
-- NB : statement looks really unreadable
lemma supp_quot_supp {Γ : Type*} [linear_ordered_comm_group Γ]
  {R : Type*} [comm_ring R] (v : valuation R Γ) {J : ideal R} (hJ : J ≤ supp v):
supp (extension_to_quot v hJ) = ideal.map (ideal.quotient.mk J) (supp v) :=
begin
  apply le_antisymm,
  { rintro ⟨x⟩ hx,
    apply ideal.subset_span,
    refine ⟨x, hx, rfl⟩, },
  { rw ideal.map_le_iff_le_comap,
    intros x hx, exact hx }
end

end supp

section quotient_ring
open localization

-- Kenny says this should work for nonzero commrings
-- ne_zero_of_mem_non_zero_divisors uses integral domain though -- maybe it shouldn't
-- oh wait -- support is a prime ideal so if it's zero the ring is an ID anyway
/-- extension of valuation on ID with support 0 to field of fractions -/
definition extension_to_frac {Γ : Type*} [linear_ordered_comm_group Γ]
  {R : Type*} [integral_domain R] (v : valuation R Γ) (hv : supp v = 0) :
quotient_ring R → with_zero Γ :=
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
  have hvs : v s ≠ 0 := λ H, hs $ (submodule.mem_bot R).1 (lattice.eq_bot_iff.1 hv H),
  have hvu : v u ≠ 0 := λ H, hu $ (submodule.mem_bot R).1 (lattice.eq_bot_iff.1 hv H),
  have hvw : v w ≠ 0 := λ H, hw $ (submodule.mem_bot R).1 (lattice.eq_bot_iff.1 hv H),
  rw [with_zero.div_eq_div hvs hvu],
  rw [sub_mul, sub_eq_zero] at h, replace h := congr_arg v h,
  iterate 4 { rw map_mul at h },
  cases option.is_some_iff_exists.1 (is_some_iff_ne_none.2 hvw) with w hvw, rw hvw at h, rw mul_comm,
  cases v s * v t; cases v u * v r, { refl }, { simpa using h }, { simpa using h },
  congr' 1, replace h := option.some.inj h, symmetry, exact mul_right_cancel h
end

-- TODO Does this work yet?
-- example (R : Type*) [integral_domain R] : discrete_field (quotient_ring R) := by apply_instance
-- If it does, then mathlib fixed the problem and the next line can be removed
instance (R : Type*) [integral_domain R] : discrete_field (quotient_ring R) := quotient_ring.field.of_integral_domain R

end quotient_ring

#exit
--section discrete_field

variable (v)

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

variables {R : Type u₁} [comm_ring R] [decidable_eq R]

-- This structure is scary because it has a random Γ : Type u₁ inside, but
-- we don't use it very often; it's an intermediate thing.
structure minimal_valuation.parametrized_subgroup (Γ₂ : Type u₂) [linear_ordered_comm_group Γ₂] :=
(Γ : Type u₁)
[grp : comm_group Γ]
(inc : Γ → Γ₂)
[hom : is_group_hom inc]
(inj : function.injective inc)

local attribute [instance] parametrized_subgroup.grp
local attribute [instance] parametrized_subgroup.hom

variables {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]
variables (v₂ : valuation R Γ₂)

include R v₂

-- Why do we need this?
set_option class.instance_max_depth 41

-- This definition helps resolve the set-theoretic issues caused by the
-- fact that the adic spectrum of R is all equivalence classes of
-- valuations, where the value group can vary arbitrarily. It shows
-- that if v : R → {0} ∪ Γ₂ and if R has type Type u₁ then v is equivalent
-- to a valuation taking values in {0} ∪ Γ₁ with Γ₁ also of type u₁.
def minimal_value_group : minimal_valuation.parametrized_subgroup Γ₂ :=
begin
  let FG : Type u₁ := multiplicative (R →₀ ℤ), -- free ab group on R
  let φ₀ : R → Γ₂ := λ r, option.get_or_else (v₂ r) 1,
  let φ : FG → Γ₂ := λ f, finsupp.prod f (λ r n, (φ₀ r) ^ n),
  haveI : is_group_hom φ :=
    ⟨λ a b, finsupp.prod_add_index (λ a, rfl) (λ a b₁ b₂, gpow_add (φ₀ a) b₁ b₂)⟩,

  exact
  { Γ     :=  quotient (is_group_hom.ker φ),
    inc   :=  lift (is_group_hom.ker φ) φ (λ _,(is_group_hom.mem_ker φ).1),
    hom   := quotient_group.is_group_hom_quotient_lift _ _ _,
    inj   := injective_ker_lift φ }
end

namespace minimal_value_group

-- This function eats an arbitrary valuation and returns an auxiliary
-- function from R to the minimal value group, a group in the same universe as R.
-- Note that it is not a valuation, as the value 0 is not allowed; stuff in the
-- support of v gets sent to 1 not 0. This is an auxiliary function which
-- we probably won't be using outside this file if we get the API right.
def mk (r : R) : (minimal_value_group v₂).Γ :=
begin
  let FG : Type u₁ := multiplicative (R →₀ ℤ), -- free ab group on R
  let φ₀ : R → Γ₂ := λ r, option.get_or_else (v₂ r) 1,
  let φ : FG → Γ₂ := λ f, finsupp.prod f (λ r n,(φ₀ r) ^ n),
  haveI : is_group_hom φ :=
    ⟨λ a b, finsupp.prod_add_index (λ a, rfl) (λ a b₁ b₂, gpow_add (φ₀ a) b₁ b₂)⟩,

  exact quotient_group.mk (finsupp.single r (1 : ℤ))
end

-- the auxiliary function agrees with v₂ away from the support.
lemma mk_some {r : R} {g : Γ₂} (h : v₂ r = some g) :
  v₂ r = some ((minimal_value_group v₂).inc (mk v₂ r)) :=
begin
  rw h,
  congr' 1,
  dsimp [minimal_value_group, minimal_value_group.mk],
  rw finsupp.prod_single_index ; finish
end

-- the minimal value group is isomorphic to a subgroup of Γ₂ so inherits an order.
instance : linear_ordered_comm_group (minimal_value_group v₂).Γ :=
begin
  cases minimal_value_group v₂ with Γ₁ _ ψ _ inj,

  letI Γ₁linord : linear_order Γ₁ :=
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
definition minimal_valuation.val (r : R) : with_zero ((minimal_value_group v₂).Γ) :=
match v₂ r with
| some _ := some (minimal_value_group.mk v₂ r)
| 0 := 0
end

namespace minimal_valuation

@[simp] lemma zero {r} (h : v₂ r = 0) : val v₂ r = 0 :=
by simp [val, h]

lemma some {r} {g} (h : v₂ r = some g) : val v₂ r = some (minimal_value_group.mk v₂ r) :=
by simp [val, h]

lemma map (r : R) :
with_zero.map (minimal_value_group v₂).inc (val v₂ r) = v₂ r :=
begin
  destruct (v₂ r),
  { intro h, change v₂ r = 0 at h,
    simp [zero v₂ h, h], },
  { intros g h,
    rw [minimal_value_group.mk_some v₂ h, some v₂ h, with_zero.map_some] },
end

end minimal_valuation

-- the map from valuations to minimal valuations
def minimal_valuation : valuation R (minimal_value_group v₂).Γ :=
{ val := minimal_valuation.val v₂,
  property := let Γ₁ := minimal_value_group v₂ in
    valuation_of_valuation (minimal_valuation.map v₂) (λ g h, iff.refl _) Γ₁.inj (v₂.property) }

-- Definition of equivalence relation on valuations
def is_equiv {R : Type u₁} [comm_ring R]
  {Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁]
  {Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂]
  (v₁ : valuation R Γ₁) (v₂ : valuation R Γ₂) : Prop :=
∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s

def equiv_symm {R : Type u₁} [comm_ring R]
  {Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁]
  {Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂]
  {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} :
is_equiv v₁ v₂ → is_equiv v₂ v₁ := λ h r s, iff.symm (h r s)

-- Theorem that valuation v₂ is equivalent to the associated minimal valuation.
lemma minimal_valuation_equiv :
is_equiv (v₂.minimal_valuation : valuation R (minimal_value_group v₂).Γ) v₂ :=
le_of_le (minimal_valuation.map v₂) (λ g h, iff.refl _)

-- Wedhorm 1.27 iii -> ii prep
def supp_sub_of_is_equiv {R : Type u₁} [comm_ring R]
  {Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁]
  {Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂]
  {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂}
  (h : is_equiv v₁ v₂) :
((supp v₁) : set R) ⊆ supp v₂ :=
λ r Hr, by rwa [mem_supp_iff', eq_zero_iff_le_zero, ←(h r 0), ←eq_zero_iff_le_zero, ←mem_supp_iff']

/-- Wedhorm 1.27 iii -> ii -/
def supp_eq_if_is_equiv {R : Type u₁} [comm_ring R]
  {Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁]
  {Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂]
  {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂}
  (h : is_equiv v₁ v₂) :
supp v₁ = supp v₂ :=
le_antisymm (supp_sub_of_is_equiv h) $ supp_sub_of_is_equiv $ equiv_symm h

-- Notes: if v1 equiv v2 then we need a bijection from the image of v1 to the
-- image of v2; we need that the supports are the same; we need that
-- the minimal_value_group for v2 is isomorphic to the subgroup of Gamma_2 generated
-- by the image of the stuff not in the support.
-- More notes: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/eq.2Erec.20goal

-- Theorem we almost surely need -- two equivalence valuations have isomorphic
-- value groups. But we're not ready for it yet.

-- Idea: prove Wedhorn 1.27.
def minimal_valuations_biject_of_equiv {R : Type u₁} [comm_ring R]
{Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁]
{Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂]
(v₁ : valuation R Γ₁) (v₂ : valuation R Γ₂) (h : is_equiv v₁ v₂) :
(minimal_value_group v₁).Γ  → (minimal_value_group v₂).Γ :=
λ g, begin
  induction g with g g₁ g₂ h12,
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
  simp,
  dsimp,
  -- I am in eq.rec hell
  sorry
end

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
