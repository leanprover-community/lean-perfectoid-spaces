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
import data.equiv.basic
import for_mathlib.rings
import data.quot
import group_theory.quotient_group

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

/-- Γ-valued valuations on R -/
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

instance is_group_hom.unit_map : is_group_hom (unit_map v) :=
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

end -- section

/-- f : S → R induces map valuation R Γ → valuation S Γ -/
def comap {S : Type u₁} [comm_ring S] (f : S → R) [is_ring_hom f] : valuation S Γ :=
{ val := v ∘ f,
  property := by constructor;
    simp [is_ring_hom.map_zero f, is_ring_hom.map_one f,
      is_ring_hom.map_mul f, is_ring_hom.map_add f] }

lemma comap_id : v.comap (id : R → R) = v := subtype.eq rfl

lemma comap_comp {S₁ : Type u₁} [comm_ring S₁] {S₂ : Type u₂} [comm_ring S₂]
(f : S₁ → S₂) [is_ring_hom f] (g : S₂ → R) [is_ring_hom g] :
  v.comap (g ∘ f) = (v.comap g).comap f :=
subtype.ext.mpr $ rfl

def map {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
  (f : Γ → Γ₁) [is_group_hom f] (hf : monotone f) :
valuation R Γ₁ :=
{ val := with_zero.map f ∘ v,
  property :=
  { map_zero := by simp [with_zero.map_zero],
    map_one :=
    begin
      show with_zero.map f (_) = 1,
      erw [v.map_one, with_zero.map_some, is_group_hom.one f],
      refl
    end,
    map_mul := λ x y,
    begin
      delta function.comp,
      erw [v.map_mul, with_zero.map_mul f],
      refl
    end,
    map_add := λ x y,
    begin
      delta function.comp,
      apply (v.map_add x y).imp _ _;
      exact λ h, with_zero.map_monotone hf h,
    end } }

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
        split_ifs with hxy hx hy hy hx hy hy,
        { simp },
        { simp },
        { simp },
        { exfalso, cases ideal.is_prime.mem_or_mem prime hxy with h' h',
          { exact hx h' },
          { exact hy h' } },
        { exfalso, exact hxy (S.mul_mem_right hx) },
        { exfalso, exact hxy (S.mul_mem_right hx) },
        { exfalso, exact hxy (S.mul_mem_left hy) },
        { simp },
      end,
    map_add  := λ x y, begin
        split_ifs with hxy hx hy _ hx hy; try {simp};
        try {left; exact le_refl _};
        try {right}; try {exact le_refl _},
        { have hxy' : x + y ∈ S := S.add_mem hx hy,
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
@[simp] lemma mem_supp_iff' (x : R) : x ∈ (supp v : set R) ↔ v x = 0 := iff.rfl

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
lemma val_add_supp_aux (a s : R) (h : v s = 0) : v (a + s) ≤ v a :=
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
  rwa ←ideal.neg_mem_iff at h,
end

-- Function corresponding to extension of a valuation on R to a valuation on R / J if J is in the support -/
definition on_quot_val {J : ideal R} (hJ : J ≤ supp v) :
  J.quotient → with_zero Γ :=
λ q, quotient.lift_on' q v $ λ a b h,
begin
  have hsupp : a - b ∈ supp v := hJ h,
  convert val_add_supp v b (a - b) hsupp,
  simp,
end

-- Proof that function is a valuation.
variable {v}
instance on_quot_val.is_valuation {J : ideal R} (hJ : J ≤ supp v) :
is_valuation (on_quot_val v hJ) :=
{ map_zero := v.map_zero,
  map_one  := v.map_one,
  map_mul  := λ xbar ybar, quotient.ind₂' v.map_mul xbar ybar,
  map_add  := λ xbar ybar, quotient.ind₂' v.map_add xbar ybar }

-- Now the valuation
variable (v)
/-- Extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
definition on_quot {J : ideal R} (hJ : J ≤ supp v) :
  valuation J.quotient Γ :=
{ val := v.on_quot_val hJ,
  property := on_quot_val.is_valuation hJ }

@[simp] lemma on_quot_comap_eq {J : ideal R} (hJ : J ≤ supp v) :
  (v.on_quot hJ).comap (ideal.quotient.mk J) = v :=
subtype.ext.mpr $ funext $
  λ r, @quotient.lift_on_beta _ _ (J.quotient_rel) v
  (λ a b h, have hsupp : a - b ∈ supp v := hJ h,
    by convert val_add_supp v b (a - b) hsupp; simp) _

lemma comap_supp {S : Type u₁} [comm_ring S] (f : S → R) [is_ring_hom f] :
  supp (v.comap f) = ideal.comap f v.supp :=
ideal.ext $ λ x,
begin
  rw [mem_supp_iff, ideal.mem_comap, mem_supp_iff],
  refl,
end

@[simp] lemma comap_on_quot_eq (J : ideal R) (v : valuation J.quotient Γ) :
  (v.comap (ideal.quotient.mk J)).on_quot
  (by rw [comap_supp, ← ideal.map_le_iff_le_comap]; simp)
  = v :=
subtype.ext.mpr $ funext $
begin
  rintro ⟨x⟩,
  dsimp [on_quot, on_quot_val, comap, function.comp],
  show quotient.lift_on _ _ _ = _,
  erw quotient.lift_on_beta,
  refl,
end

/-- quotient valuation on R/J has support supp(v)/J if J ⊆ supp v-/
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

section fraction_ring
open localization

variables [integral_domain R]
variables {Γ : Type u} [linear_ordered_comm_group Γ] (v : valuation R Γ)

-- function corresponding to extension of valuation on ID with support 0
-- to valuation on field of fractions
definition on_frac_val (hv : supp v = 0) : fraction_ring R → with_zero Γ :=
quotient.lift (λ rs, v rs.1 / v rs.2.1 : R × non_zero_divisors R → with_zero Γ)
begin
  intros a b hab,
  rcases a with ⟨r,s,hs⟩,
  rcases b with ⟨t,u,hu⟩,
  rcases hab with ⟨w,hw,h⟩, classical,
  change v r / v s = v t / v u,
  change (s * t - (u * r)) * w = 0 at h,
  replace hs := ne_zero_of_mem_non_zero_divisors hs,
  replace hu := ne_zero_of_mem_non_zero_divisors hu,
  replace hw := ne_zero_of_mem_non_zero_divisors hw,
  have hvs : v s ≠ 0 := λ H, hs ((submodule.mem_bot R).mp (lattice.eq_bot_iff.1 hv H)),
  have hvu : v u ≠ 0 := λ H, hu ((submodule.mem_bot R).mp (lattice.eq_bot_iff.1 hv H)),
  have hvw : v w ≠ 0 := λ H, hw ((submodule.mem_bot R).mp (lattice.eq_bot_iff.1 hv H)),
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

def on_frac_val.is_valuation (hv : supp v = 0) : is_valuation (v.on_frac_val hv) :=
{ map_zero := show v.on_frac_val hv (quotient.mk' ⟨0,1⟩) = 0, by simp,
  map_one  := show v.on_frac_val hv (quotient.mk' ⟨_,1⟩) = 1, by simp,
  map_mul  := λ xbar ybar, quotient.ind₂' (λ x y,
  begin
    change v(x.1 * y.1) * (v((x.2 * y.2).val))⁻¹ =
      v(x.1) * (v(x.2.val))⁻¹ * (v(y.1) * (v(y.2.val))⁻¹),
    erw [v.map_mul, v.map_mul, with_zero.mul_inv_rev],
    simp [mul_assoc, mul_comm, mul_left_comm]
  end) xbar ybar,
  map_add  := λ xbar ybar, quotient.ind₂' (λ x y,
  begin
    let x_plus_y : fraction_ring R :=
      ⟦⟨x.2 * y.1 + y.2 * x.1, _, is_submonoid.mul_mem x.2.2 y.2.2⟩⟧,
    change on_frac_val v hv x_plus_y ≤ _ * _ ∨ on_frac_val v hv x_plus_y ≤ _ * _,
    dsimp,
    cases (is_valuation.map_add v (x.2 * y.1) (y.2 * x.1)) with h h;
    [right, left];
    refine le_trans (linear_ordered_comm_monoid.mul_le_mul_right h _) _;
    erw [v.map_mul, v.map_mul, with_zero.mul_inv_rev];
    refine le_trans (le_of_eq _)
      (le_trans (linear_ordered_comm_monoid.mul_le_mul_right
        (mul_inv_self $ v (_ : R × (non_zero_divisors R)).snd.val) _) $
        le_of_eq $ one_mul _),
    { exact x },
    { repeat {rw [mul_assoc]}, congr' 1,
      rw [← mul_assoc, mul_comm], },
    { exact y },
    { repeat {rw [mul_assoc]}, congr' 1,
      rw mul_left_comm, },
  end) xbar ybar }

/-- Extension of valuation on R with supp 0 to valuation on field of fractions -/
def on_frac (hv : supp v = 0) : valuation (fraction_ring R) Γ :=
{ val := on_frac_val v hv,
  property := on_frac_val.is_valuation v hv }

lemma on_frac_val' (hv : supp v = 0) (q : fraction_ring R) :
  v.on_frac hv q = v.on_frac_val hv q := rfl

@[simp] lemma on_frac_comap_eq (hv : supp v = 0) :
  (v.on_frac hv).comap (fraction_ring.inc R) = v :=
subtype.ext.mpr $ funext $ λ r, show v r / v 1 = v r, by simp

@[simp] lemma comap_on_frac_eq (v : valuation (fraction_ring R) Γ) :
  (v.comap (fraction_ring.inc R)).on_frac
  (by {rw [comap_supp, ideal.zero_eq_bot, (supp v).eq_bot_of_prime],
    apply ideal.comap_bot_of_inj, apply fraction_ring.inc.injective })
  = v :=
subtype.ext.mpr $ funext $
begin
  rintro ⟨x⟩,
  dsimp [on_frac, on_frac_val, comap, function.comp],
  erw quotient.lift_beta,
  change v (fraction_ring.inc R x.1) /
         v (fraction_ring.inc R x.2.val) = _,
  rw with_zero.div_eq_iff_mul_eq,
  { erw ← v.map_mul,
    apply congr_arg,
    change ⟦_⟧ = ⟦_⟧,
    apply quotient.sound,
    dsimp [(≈), setoid.r],
    erw localization.r_iff _ _,
    use 1,
    split, swap, dsimp, rw [mul_one, mul_one], ring,
    apply mem_non_zero_divisors_of_ne_zero, simp},
  intro h,
  rw [← mem_supp_iff, (supp v).eq_bot_of_prime] at h,
  simp at h,
  replace h := eq_zero_of _ h,
  refine localization.ne_zero_of_mem_non_zero_divisors _ h,
  exact x.2.2
end

end fraction_ring

variables [comm_ring R]
variables {Γ : Type u} [linear_ordered_comm_group Γ] (v : valuation R Γ)

definition valuation_field_aux := (supp v).quotient

instance : integral_domain (valuation_field_aux v) := by delta valuation_field_aux; apply_instance

definition valuation_field := localization.fraction_ring (valuation_field_aux v)

instance : discrete_field (valuation_field v) := by delta valuation_field; apply_instance

section
open ideal

definition on_valuation_field : valuation (valuation_field v) Γ :=
on_frac (v.on_quot (set.subset.refl _))
begin
  rw [supp_quot_supp],
  rw zero_eq_bot,
  apply ideal.map_quotient_self,
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
  { exact λ (H : _ < _), ne_of_lt H (map_one _) },
  { rintros J ⟨x,hx⟩ hJ hxni hxinJ,
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

-- Johan: this should be a discrete field, I think
-- Kevin doesn't really know the difference between a field and a discrete field :-/
instance : field (residue_field v) := ideal.quotient.field _

section canonical_equivalent_valuation

definition valuation_field_units := is_group_hom.ker v.on_valuation_field.unit_map

instance (v : valuation R Γ) : is_subgroup (valuation_field_units v) :=
by unfold valuation_field_units; apply_instance

instance : comm_group (units (valuation_field v)) := by apply_instance

def canonical_ordered_group (v : valuation R Γ) : Type u₀ :=
quotient_group.quotient (valuation_field_units v)

def canonical_ordered_group_quotient (v : valuation R Γ) :
units (valuation_field v) → canonical_ordered_group v :=
quotient.mk'

instance canonical_ordered_group.comm_group : comm_group (canonical_ordered_group v) :=
by unfold canonical_ordered_group; apply_instance

instance canonical_ordered_group_quotient.is_group_hom :
is_group_hom (canonical_ordered_group_quotient v) := ⟨λ _ _, rfl⟩

instance : linear_order (canonical_ordered_group v) :=
{ le := λ a' b', quotient.lift_on₂' a' b' (λ s t, v.on_valuation_field s ≤ v.on_valuation_field t) $
    λ a b c d hac hbd, begin
      change a⁻¹ * c ∈ is_group_hom.ker v.on_valuation_field.unit_map at hac,
      change b⁻¹ * d ∈ is_group_hom.ker v.on_valuation_field.unit_map at hbd,
      rw [is_group_hom.mem_ker, mul_comm, ←is_group_hom.one_iff_ker_inv] at hac hbd,
      show (on_valuation_field v) a ≤ (on_valuation_field v) b =
    ((on_valuation_field v) c ≤ (on_valuation_field v) d),
      rw [←unit_map_eq, ←unit_map_eq, ←unit_map_eq, ←unit_map_eq, hbd, hac]
    end,
  le_refl := λ abar, quotient.induction_on' abar $ λ a, le_refl ((on_valuation_field v) a),
  le_trans := λ abar bbar cbar, quotient.induction_on₃' abar bbar cbar $ λ a b c,
    @le_trans _ _ ((on_valuation_field v) a) ((on_valuation_field v) b) ((on_valuation_field v) c),
  le_antisymm := λ abar bbar, quotient.induction_on₂' abar bbar $ λ a b hab hba, begin
    have h :=  @le_antisymm _ _ ((on_valuation_field v) a) ((on_valuation_field v) b) hab hba,
    apply quotient.sound,
    change a⁻¹ * b ∈ is_group_hom.ker v.on_valuation_field.unit_map,
    rw [is_group_hom.mem_ker, mul_comm, ←is_group_hom.one_iff_ker_inv],
    rw [←unit_map_eq, ←unit_map_eq] at h,
    replace h := option.injective_some _ h,
    rw h,
  end,
  le_total := λ abar bbar, quotient.induction_on₂' abar bbar $ λ a b,
    le_total ((on_valuation_field v) a) ((on_valuation_field v) b),
}

instance : linear_ordered_comm_group (canonical_ordered_group v) :=
{ mul_le_mul_left := begin rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩,
    change v.on_valuation_field a ≤ v.on_valuation_field b at h,
    change canonical_ordered_group_quotient v c * canonical_ordered_group_quotient v a
    ≤ canonical_ordered_group_quotient v c * canonical_ordered_group_quotient v b,
    rw ←is_group_hom.mul (canonical_ordered_group_quotient v),
    rw ←is_group_hom.mul (canonical_ordered_group_quotient v),
    change v.on_valuation_field (c * a) ≤ v.on_valuation_field (c * b),
    rw v.on_valuation_field.map_mul,
    rw v.on_valuation_field.map_mul,
    exact with_zero.mul_le_mul_left _ _ h _
end}

-- Tbe canonical valuation associated to v is the obvious map
-- from R to canonical_ordered_group v := Frac(R/supp(v)) / A^*
-- (thought of as K^*/A^* union 0)

-- First define a valuation on K
definition valuation_field.canonical_valuation_v : valuation_field v → with_zero (canonical_ordered_group v) :=
λ k, dite (k = 0) (λ _, 0)
  (λ h, canonical_ordered_group_quotient v ⟨k,k⁻¹,mul_inv_cancel h, inv_mul_cancel h⟩)

instance valuation_field.canonical_valuation_v.is_valuation : is_valuation (valuation_field.canonical_valuation_v v) :=
{ map_zero := dif_pos rfl,
  map_one := begin unfold valuation_field.canonical_valuation_v, rw dif_neg zero_ne_one.symm,
    apply option.some_inj.2,
    convert is_group_hom.one (canonical_ordered_group_quotient v),
    exact inv_one
  end,
  map_mul := λ x y, begin
    unfold valuation_field.canonical_valuation_v,
    split_ifs with hxy hx hy hy hx hy hy EEE FFF GGG HHH,
    { simp },
    { simp },
    { simp },
    { exfalso, exact or.elim (mul_eq_zero.1 hxy) hx hy},
    { exfalso, exact hxy (hx.symm ▸ zero_mul y)},
    { exfalso, exact hxy (hx.symm ▸ zero_mul y)},
    { exfalso, exact hxy (hy.symm ▸ mul_zero x)},
--    show some _ = some _,
    apply option.some_inj.2,
    show canonical_ordered_group_quotient v {val := x * y, inv := (x * y)⁻¹, val_inv := _, inv_val := _} =
    canonical_ordered_group_quotient v {val := x * y, inv := _, val_inv := _, inv_val := _},
    apply congr_arg,
    apply units.ext,
    refl,
  end,
  map_add := λ x y, begin
    unfold valuation_field.canonical_valuation_v,
    split_ifs with hxy hx hy hy hx hy hy EEE FFF GGG HHH,
    { left, exact le_refl _ },
    { left, exact le_refl _ },
    { right, exact le_refl _ },
    { left, exact zero_le },
    { exfalso, exact hxy (hx.symm ▸ hy.symm ▸ add_zero _)},
    { right, convert le_refl _; rw hx; exact (zero_add y).symm },
    { left, convert le_refl _; rw hy; exact (add_zero x).symm },
    { rw [with_bot.coe_le_coe,with_bot.coe_le_coe],
      exact v.on_valuation_field.map_add _ _ }
  end }

def valuation_field.canonical_valuation :
valuation (valuation_field v) (canonical_ordered_group v) :=
⟨valuation_field.canonical_valuation_v v, valuation_field.canonical_valuation_v.is_valuation v⟩

definition quotient.canonical_valuation (v : valuation R Γ) :
valuation (ideal.quotient (supp v)) (canonical_ordered_group v) :=
comap (valuation_field.canonical_valuation v) (localization.fraction_ring.inc _)

definition canonical_valuation (v : valuation R Γ) :
valuation R (canonical_ordered_group v) :=
comap (quotient.canonical_valuation v) (ideal.quotient.mk (supp v))

end canonical_equivalent_valuation

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
-- valuations, where the value group can vary in an arbitrary universe. It shows
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

lemma on_quot_comap_self {J : ideal R} (hJ : J ≤ supp v) :
  is_equiv ((v.on_quot hJ).comap (ideal.quotient.mk J)) v :=
of_eq (on_quot_comap_eq _ _)

lemma comap_on_quot (J : ideal R) (v₁ : valuation J.quotient Γ₁) (v₂ : valuation J.quotient Γ₂) :
  (v₁.comap (ideal.quotient.mk J)).is_equiv (v₂.comap (ideal.quotient.mk J)) ↔ v₁.is_equiv v₂ :=
{ mp  := begin rintros h ⟨x⟩ ⟨y⟩, exact h x y end,
  mpr := λ h, comap _ h }

open localization

lemma on_frac_comap_self {R : Type u₀} [integral_domain R] (v : valuation R Γ) (hv : supp v = 0) :
  is_equiv ((v.on_frac hv).comap (fraction_ring.inc R)) v :=
of_eq (on_frac_comap_eq v hv)

lemma comap_on_frac {R : Type u₀} [integral_domain R]
(v₁ : valuation (fraction_ring R) Γ₁) (v₂ : valuation (fraction_ring R) Γ₂) :
  is_equiv (v₁.comap (fraction_ring.inc R))
           (v₂.comap (fraction_ring.inc R)) ↔
  is_equiv v₁ v₂ :=
{ mp  := begin
    rintros h ⟨x⟩ ⟨y⟩,
    erw ← comap_on_frac_eq v₁,
    erw ← comap_on_frac_eq v₂,
    dsimp [comap],
    repeat {erw on_frac_val'},
    repeat {erw on_frac_val_mk},
    repeat {erw with_zero.div_le_div},
    repeat {erw ← valuation.map_mul},
    exact h _ _,
    all_goals { intro H,
      erw [← mem_supp_iff, comap_supp, (supp _).eq_bot_of_prime] at H,
      simp at H,
      replace H := eq_zero_of _ H,
      refine localization.ne_zero_of_mem_non_zero_divisors _ H,
      apply val_prop _,
      apply_instance },
  end,
  mpr := λ h, comap _ h }

/-- Wedhorm 1.27 iii -> ii (part a) -/
lemma supp_eq (h : v₁.is_equiv v₂) : supp v₁ = supp v₂ :=
ideal.ext $ λ r,
calc r ∈ supp v₁ ↔ v₁ r = 0    : mem_supp_iff' _ _
             ... ↔ v₁ r ≤ v₁ 0 : eq_zero_iff_le_zero _
             ... ↔ v₂ r ≤ v₂ 0 : h r 0
             ... ↔ v₂ r = 0    : (eq_zero_iff_le_zero _).symm
             ... ↔ r ∈ supp v₂ : (mem_supp_iff' _ _).symm

end is_equiv

section
variables {v : valuation R Γ} {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} {v₃ : valuation R Γ₃}

open is_group_hom quotient_group function

def quot_of_quot_of_eq_supp (h : supp v₁ = supp v₂) : (supp v₁).quotient → (supp v₂).quotient :=
ideal.quotient.lift _ (ideal.quotient.mk _)
begin
  intros r hr,
  rwa [ideal.quotient.eq_zero_iff_mem, ←h]
end

@[simp] lemma quot_of_quot_of_eq_supp_quotient_mk (h : supp v₁ = supp v₂) :
  quot_of_quot_of_eq_supp h ∘ ideal.quotient.mk _ = ideal.quotient.mk _ :=
funext $ λ x, ideal.quotient.lift_mk

instance (h : supp v₁ = supp v₂) : is_ring_hom (quot_of_quot_of_eq_supp h) :=
by delta quot_of_quot_of_eq_supp; apply_instance

def quot_equiv_quot_of_eq_supp (h : supp v₁ = supp v₂) : (supp v₁).quotient ≃ (supp v₂).quotient :=
{ to_fun := quot_of_quot_of_eq_supp h,
  inv_fun := quot_of_quot_of_eq_supp h.symm,
  left_inv :=
  begin
    rintro ⟨q⟩,
    delta quot_of_quot_of_eq_supp,
    erw ideal.quotient.lift_mk,
    refl
  end,
  right_inv :=
  begin
    rintro ⟨q⟩,
    delta quot_of_quot_of_eq_supp,
    erw ideal.quotient.lift_mk,
    refl
  end }

@[simp] lemma quot_equiv_quot_of_eq_supp_coe (h : supp v₁ = supp v₂) :
  (quot_equiv_quot_of_eq_supp h : (supp v₁).quotient → (supp v₂).quotient) = quot_of_quot_of_eq_supp h := rfl

instance grmbl (h : supp v₁ = supp v₂) : is_ring_hom (quot_equiv_quot_of_eq_supp h) :=
by simp; apply_instance

lemma quot_of_quot_of_eq_supp_inj (h : supp v₁ = supp v₂) : injective (quot_of_quot_of_eq_supp h) :=
injective_of_left_inverse (quot_equiv_quot_of_eq_supp h).left_inv

section
open localization

def valfield_of_valfield_of_eq_supp (h : supp v₁ = supp v₂) :
  valuation_field v₁ → valuation_field v₂ :=
frac_map (quot_of_quot_of_eq_supp h) (quot_of_quot_of_eq_supp_inj h)

instance bar (h : supp v₁ = supp v₂) : is_field_hom (valfield_of_valfield_of_eq_supp h) :=
by delta valfield_of_valfield_of_eq_supp; apply_instance

def valfield_equiv_valfield_of_eq_supp (h : supp v₁ = supp v₂) : valuation_field v₁ ≃ valuation_field v₂ :=
frac_equiv_frac_of_equiv (quot_equiv_quot_of_eq_supp h)

instance barz (h : supp v₁ = supp v₂) :
  is_field_hom (valfield_equiv_valfield_of_eq_supp h) := valuation.bar h

end

-- lemma ker_eq_ker_of_equiv (h : v₁.is_equiv v₂) :
--   ker (of_free_group v₁) = ker (of_free_group v₂) :=
-- begin
--   ext f,
--   split; rw [mem_ker, mem_ker]; intro hf,
-- end

-- why is this not in the library???
-- there are other theorems about strict monos!!!
lemma monotone_of_strict_mono {α β} [linear_order α] [preorder β]
{f : α → β} (H : ∀ a b, a < b → f a < f b) :
  monotone f :=
λ a b, iff.mpr $ le_iff_le_of_strict_mono _ H

lemma of_map_of_strict_mono {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁] (f : Γ → Γ₁) [is_group_hom f]
-- for some reason there is no definition of strict monos. But there are theorems about them.
(H : ∀ a b, a < b → f a < f b) :
  is_equiv (v.map f (monotone_of_strict_mono H)) v :=
begin
  intros x y,
  split,
  swap,
  intro h,
  exact with_zero.map_monotone (monotone_of_strict_mono H) h,
  change with_zero.map f _ ≤ with_zero.map f _ → _,
  refine (le_iff_le_of_strict_mono _ _).mp,
  exact with_zero.map_strict_mono H
end

-- Wedhorn 1.27 (i) => (iii)
lemma of_inj_value_group (f : v₁.minimal_value_group.Γ → v₂.minimal_value_group.Γ)
[is_group_hom f] (H : ∀ a b, a < b → f a < f b)
(H : v₂.minimal_valuation = v₁.minimal_valuation.map f (monotone_of_strict_mono H)) :
  v₁.is_equiv v₂ :=
begin
  refine is_equiv.trans _ (v₂.minimal_valuation_is_equiv),
  refine is_equiv.trans (v₁.minimal_valuation_is_equiv.symm) _,
  rw H,
  symmetry,
  exact of_map_of_strict_mono _ _
end

lemma is_equiv.comap_quot_of_quot (h : v₁.is_equiv v₂) :
  (v₁.on_quot (set.subset.refl _)).is_equiv
  (comap (v₂.on_quot (set.subset.refl _)) (quot_of_quot_of_eq_supp h.supp_eq)) :=
begin
  rw [← is_equiv.comap_on_quot, ← comap_comp],
  simp [h],
end

lemma is_equiv.on_valuation_field_is_equiv (h : v₁.is_equiv v₂) :
  v₁.on_valuation_field.is_equiv
  (comap v₂.on_valuation_field (valfield_of_valfield_of_eq_supp h.supp_eq)) :=
begin
  delta valfield_of_valfield_of_eq_supp, delta on_valuation_field,
  erw [← is_equiv.comap_on_frac, ← comap_comp, on_frac_comap_eq],
  simp [comap_comp, h.comap_quot_of_quot],
end

def val_ring_equiv_of_is_equiv (h : v₁.is_equiv v₂) : v₁.valuation_ring ≃ v₂.valuation_ring :=
equiv.subtype_congr (valfield_equiv_valfield_of_eq_supp h.supp_eq)
begin
  intro x,
  show _ ≤ _ ↔ _ ≤ _,
  erw [← v₁.on_valuation_field.map_one, h.on_valuation_field_is_equiv],
  convert iff.refl _,
  symmetry,
  exact valuation.map_one _,
end

-- Wedhorn 1.27 (iii) => (ii)b
instance xyzzy (h : v₁.is_equiv v₂) : is_ring_hom (val_ring_equiv_of_is_equiv h) :=
begin
  cases (by apply_instance : is_ring_hom (valfield_equiv_valfield_of_eq_supp h.supp_eq)),
  constructor,
  all_goals {
    intros,
    apply subtype.val_injective,
    apply_assumption, },
end

-- Notes: if v1 equiv v2 then we need a bijection from the image of v1 to the
-- image of v2; we need that the supports are the same; we need that
-- the minimal_value_group for v2 is isomorphic to the subgroup of Γ₂ generated
-- by the image of the stuff not in the support.
-- More notes: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/eq.2Erec.20goal

-- Theorem we almost surely need -- two equivalence valuations have isomorphic
-- value groups. But we're not ready for it yet.

def minimal_valuations_biject_of_equiv (v₁ : valuation R Γ₁) (v₂ : valuation R Γ₂) (h : is_equiv v₁ v₂) :
  (minimal_value_group v₁).Γ → (minimal_value_group v₂).Γ :=
@quotient_group.map _ _ _ _ _ _ _ _ id is_group_hom.id sorry
-- KB added sorry, I have no idea whether this used to compile or not.
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

#exit

File ends here. Below are some comments, mostly dealt with now.

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
