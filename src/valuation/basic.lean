import algebra.group_power
import ring_theory.ideal_operations
import ring_theory.subring

import for_mathlib.rings
import for_mathlib.equiv

import valuation.linear_ordered_comm_group_with_zero

/-! valuation.basic

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes "Adic Spaces" ([W])

The definition of a valuation we use here is Definition 1.22 of [W]. `valuation R Γ`
is the type of valuations R → Γ ∪ {0}, with a coercion to the underlying
function. If v is a valuation from R to Γ ∪ {0} then the induced group
homomorphism units(R) → Γ is called `unit_map v`.

The equivalence "relation" `is_equiv v₁ v₂ : Prop` defined in [W; 1.27] is not strictly
speaking a relation, because v₁ : valuation R Γ₁ and v₂ : valuation R Γ₂ might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as Γ varies) on a ring R is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) as the definition of equivalence.

The trivial valuation associated to a prime ideal P of R is `trivial P : valuation R Γ`.

The support of a valuation v : valuation R Γ is `supp v`. If J is an ideal of R
with `h : J ⊆ supp v` then the induced valuation
on R / J = `ideal.quotient J` is `on_quot v h`.

If v is a valuation on an integral domain R and `hv : supp v = 0`, then
`on_frac v hv` is the extension of v to fraction_ring R, the field of
fractions of R.

`valuation_field v`, `valuation_ring v`, `max_ideal v` and `residue_field v`
are the valuation field, valuation ring, maximal ideal and residue field
of v. See [W; 1.26].
-/

local attribute [instance] classical.prop_decidable
noncomputable theory

local attribute [instance, priority 0] classical.decidable_linear_order

open function ideal

universes u u₀ u₁ u₂ u₃ -- v is used for valuations

variables {Γ : Type u} [linear_ordered_comm_group_with_zero Γ]
variables {Γ₁ : Type u₁} [linear_ordered_comm_group_with_zero Γ₁]
variables {Γ₂ : Type u₂} [linear_ordered_comm_group_with_zero Γ₂]
variables {Γ₃ : Type u₃} [linear_ordered_comm_group_with_zero Γ₃]

variables {R : Type u₀} -- This will be a ring, assumed commutative in some sections

set_option old_structure_cmd true

/-- The type of ({0} ∪ Γ)-valued valuations on R. -/
structure valuation (R : Type u₀) [ring R] (Γ : Type u) [linear_ordered_comm_group_with_zero Γ]
  extends R →* Γ :=
(map_zero' : to_fun 0 = 0)
(map_add' : ∀ x y, to_fun (x + y) ≤ to_fun x ∨ to_fun (x + y) ≤ to_fun y)

namespace valuation

section basic
variables [ring R]

/-- A valuation is coerced to the underlying function R → {0} ∪ Γ. -/
instance (R : Type u₀) [ring R] (Γ : Type u) [linear_ordered_comm_group_with_zero Γ] :
has_coe_to_fun (valuation R Γ) := { F := λ _, R → Γ, coe := valuation.to_fun}

variables (v : valuation R Γ) {x y z : R}

@[simp] lemma map_zero : v 0 = 0 := v.map_zero'
@[simp] lemma map_one  : v 1 = 1 := v.map_one'
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := v.map_mul'
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y := v.map_add'

@[extensionality] lemma ext {v₁ v₂ : valuation R Γ} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
by { cases v₁, cases v₂, congr, funext r, exact h r }

lemma ext_iff {Γ : Type u} [linear_ordered_comm_group_with_zero Γ] {v₁ v₂ : valuation R Γ} :
  v₁ = v₂ ↔ ∀ r, v₁ r = v₂ r :=
⟨λ h r, congr_arg _ h, ext⟩

lemma map_add_le_max (x y) : v (x + y) ≤ max (v x) (v y) :=
begin
  cases map_add v x y with h,
  apply le_max_left_of_le h,
  apply le_max_right_of_le h,
end

-- The following definition is not an instance, because we have more than one v on a given R.
/-- A valuation gives a preorder on the underlying ring. -/
def to_preorder : preorder R := preorder.lift v (by apply_instance)

-- /-- If x ∈ R is a unit then v x is non-zero. -/
-- theorem map_unit (h : x * y = 1) : (v x).is_some :=
-- begin
--   have h1 := v.map_mul x y,
--   rw [h, map_one v] at h1,
--   cases (v x),
--   { exfalso,
--     exact option.no_confusion h1 },
--   { constructor }
-- end

-- /-- If x is a unit of R then there exists γ∈Γ with v(x)=γ. -/
-- lemma unit_is_some (x : units R) : ∃ γ : Γ, v x = γ :=
-- begin
--   have h1 := v.map_mul x.val x.inv,
--   rw [x.val_inv, valuation.map_one] at h1,
--   exact with_zero.eq_coe_of_mul_eq_coe_left h1.symm
-- end

-- /-- If x is a unit of R then v x is non-zero. -/
-- lemma map_unit_ne_zero (x : units R) : v x ≠ 0 :=
-- begin
--   cases unit_is_some v x with γ Hγ,
--   rw Hγ,
--   apply option.no_confusion,
-- end

/-- If v is a valuation on a division ring then v(x)=0 iff x=0. -/
lemma zero_iff {K : Type u₀} [division_ring K]
  (v : valuation K Γ) {x : K} : v x = 0 ↔ x = 0 :=
begin
  split ; intro h,
  { contrapose! h,
    exact group_with_zero.unit_ne_zero (units.map v.to_monoid_hom $ units.mk0 _ h) },
  { exact h.symm ▸ v.map_zero },
end

lemma map_inv' {K : Type u₀} [division_ring K]
  (v : valuation K Γ) {x : K} (h : x ≠ 0) : v x⁻¹ = (v x)⁻¹ :=
begin
  apply eq_inv_of_mul_right_eq_one',
  rw [← v.map_mul, mul_inv_cancel h, v.map_one]
end

lemma map_inv {K : Type u₀} [discrete_field K]
  (v : valuation K Γ) {x : K} : v x⁻¹ = (v x)⁻¹ :=
begin
  by_cases h : x = 0,
  { rw [h, _root_.inv_zero, map_zero, inv_zero'] },
  { exact v.map_inv' h }
end

lemma ne_zero_iff {Γ : Type u} [linear_ordered_comm_group_with_zero Γ] {K : Type u₀} [division_ring K]
  (v : valuation K Γ) {x : K} : v x ≠ 0 ↔ x ≠ 0 :=
not_iff_not_of_iff v.zero_iff

-- lemma coe_of_ne_zero {Γ : Type u} [linear_ordered_comm_group_with_zero Γ] {K : Type u₀} [division_ring K]
--   (v : valuation K Γ) {x : K} (h : x ≠ 0) : ∃ γ : Γ, v x = γ :=
-- by rwa [← v.ne_zero_iff, with_zero.ne_zero_iff_exists] at h

lemma map_units_inv (x : units R) : v (x⁻¹ : units R) = (v x)⁻¹ :=
eq_inv_of_mul_right_eq_one' _ _ $ by rw [← v.map_mul, units.mul_inv, v.map_one]

-- lemma map_unit' (x : units R) : (v x).is_some := map_unit v x.val_inv

-- /-- `unit_map v` is the map R^× → Γ associated to a valuation v : R → {0} ∪ Γ.-/
-- definition unit_map : units R → Γ :=
-- λ u, match v u with
-- | some x := x
-- | none := 1
-- end

@[simp] theorem unit_map_eq (u : units R) :
  (units.map v.to_monoid_hom u : Γ) = v u := rfl

-- lemma unit_map.ext (x z : units R) (H : v (z.val) = v (x.val)) :
--   valuation.unit_map v z = valuation.unit_map v x :=
-- by rwa [←option.some_inj, valuation.unit_map_eq, valuation.unit_map_eq]

-- @[simp] lemma coe_unit_map (x : units R)  : ↑(v.unit_map x) = v x :=
-- by rw ← valuation.unit_map_eq ; refl

-- /-- The unit_map associated to a valuation is a group homomorphism. -/
-- instance unit_map.is_group_hom : is_group_hom (unit_map v) :=
-- is_group_hom.mk' $
-- λ a b, option.some.inj $
--   show _ = (some _ * some _ : Γ),
--   by simp

@[simp] theorem map_neg_one : v (-1) = 1 :=
begin
  show (units.map v.to_monoid_hom (-1 : units R) : Γ) = (1 : units Γ),
  rw ← units.ext_iff,
  apply linear_ordered_structure.eq_one_of_pow_eq_one (_ : _ ^ 2 = _),
  rw [← is_monoid_hom.map_pow (units.map v.to_monoid_hom), pow_two, units.ext_iff],
  show v ((-1) * (-1)) = 1,
  rw [neg_one_mul, neg_neg, v.map_one]
end

@[simp] lemma map_neg (x : R) : v (-x) = v x :=
calc v (-x) = v (-1 * x)   : by simp
        ... = v (-1) * v x : map_mul _ _ _
        ... = v x          : by simp

lemma map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
calc v (x - y) = v (-(y - x)) : by rw show x - y = -(y-x), by abel
           ... = _ : map_neg _ _

lemma map_sub_le_max (x y : R) : v (x - y) ≤ max (v x) (v y) :=
calc v (x-y) = v (x + -y)   : by simp
        ... ≤ max (v x) (v $ -y) : map_add_le_max _ _ _
        ... = max (v x) (v y)    : by rw map_neg

lemma map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = max (v x) (v y) :=
begin
  suffices : ¬v (x + y) < max (v x) (v y),
    from or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (map_add_le_max v x y)) this,
  intro h',
  wlog vyx : v y < v x using x y,
  { apply lt_or_gt_of_ne h.symm },
  { rw max_eq_left_of_lt vyx at h',
    apply lt_irrefl (v x),
    calc v x = v ((x+y) - y)         : by simp
         ... ≤ max (v $ x + y) (v y) : map_sub_le_max _ _ _
         ... < v x                   : max_lt h' vyx },
  { apply this h.symm,
    rwa [add_comm, max_comm] at h' }
end

lemma map_eq_of_sub_lt (h : v (y - x) < v x) : v y = v x :=
begin
  have := valuation.map_add_of_distinct_val v (ne_of_gt h).symm,
  rw max_eq_right (le_of_lt h) at this,
  simpa using this
end

-- @[simp] theorem eq_zero_iff_le_zero {r : R} : v r = 0 ↔ v r ≤ v 0 :=
-- by simpa using
-- linear_ordered_comm_group_with_zero.le_zero_iff.symm

-- section change_of_group

-- variables {v₁ : R → Γ₁} {v₂ : R → Γ₂}
-- variables {ψ : Γ₁ →* Γ₂}
-- variables (H12 : ∀ r, ψ (v₁ r) = v₂ r)
-- variables (Hle : ∀ g h : Γ₁, g ≤ h ↔ ψ g ≤ ψ h)
-- -- This include statement means that we have an underlying assumption
-- -- that ψ : Γ₁ → Γ₂ is order-preserving, and that v₁ and v₂ are functions with ψ ∘ v₁ = v₂.
-- include H12 Hle

-- theorem le_of_le (r s : R) : v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s :=
-- by { rw ←H12 r, rw ←H12 s, exact Hle _ _ }

-- /-- Restriction of a Γ₂-valued valuation to a subgroup Γ₁ is still a valuation. -/
-- theorem valuation_of_valuation (Hiψ : function.injective ψ) (H : is_valuation v₂) :
-- is_valuation v₁ :=
-- { map_zero := with_zero.injective_map Hiψ $
--     by erw [H12, H.map_zero, ← with_zero.map_zero],
--   map_one := with_zero.injective_map Hiψ $
--     by erw [H12, H.map_one, with_zero.map_coe, is_group_hom.map_one ψ]; refl,
--   map_mul := λ r s, with_zero.injective_map Hiψ $
--     by rw [H12, H.map_mul, ←H12 r, ←H12 s]; exact (with_zero.map_mul _ _ _).symm,
--   map_add := λ r s,
--   begin
--     apply (H.map_add r s).imp _ _;
--     erw [with_zero.map_le Hle, ←H12, ←H12];
--     exact id
--   end }

-- end change_of_group -- section

/-- A ring homomorphism S → R induces a map valuation R Γ → valuation S Γ -/
def comap {S : Type u₁} [ring S] (f : S → R) [is_ring_hom f] (v : valuation R Γ) :
  valuation S Γ :=
by refine_struct { to_fun := v ∘ f, .. }; intros;
  simp [is_ring_hom.map_zero f, is_ring_hom.map_one f, is_ring_hom.map_mul f, is_ring_hom.map_add f]

@[simp] lemma comap_id : v.comap (id : R → R) = v := ext $ λ r, rfl

lemma comap_comp {S₁ : Type u₁} [ring S₁] {S₂ : Type u₂} [ring S₂]
(f : S₁ → S₂) [is_ring_hom f] (g : S₂ → R) [is_ring_hom g] :
  v.comap (g ∘ f) = (v.comap g).comap f :=
ext $ λ r, rfl

/-- A ≤-preserving group homomorphism Γ → Γ₁ induces a map valuation R Γ → valuation R Γ₁. -/
def map (f : Γ₁ →* Γ₂) (h₀ : f 0 = 0) (hf : monotone f) (v : valuation R Γ₁) : valuation R Γ₂ :=
{ to_fun := f ∘ v,
  map_zero' := show f (v 0) = 0, by rw [v.map_zero, h₀],
  map_add' := λ r s, by { refine (v.map_add r s).imp _ _; exact λ h, hf h },
  .. monoid_hom.comp f v.to_monoid_hom }

/-- Two valuations on R are defined to be equivalent if they induce the same preorder on R. -/
def is_equiv (v₁ : valuation R Γ₁) (v₂ : valuation R Γ₂) : Prop :=
∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s

end basic -- end of section

namespace is_equiv
variables [ring R]
variables {v : valuation R Γ}
variables {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} {v₃ : valuation R Γ₃}

@[refl] lemma refl : v.is_equiv v :=
λ _ _, iff.refl _

@[symm] lemma symm (h : v₁.is_equiv v₂) : v₂.is_equiv v₁ :=
λ _ _, iff.symm (h _ _)

@[trans] lemma trans (h₁₂ : v₁.is_equiv v₂) (h₂₃ : v₂.is_equiv v₃) : v₁.is_equiv v₃ :=
λ _ _, iff.trans (h₁₂ _ _) (h₂₃ _ _)

lemma of_eq {v' : valuation R Γ} (h : v = v') : v.is_equiv v' :=
by subst h; refl

lemma map {v' : valuation R Γ} (f : Γ →* Γ₁) (h₀ : f 0 = 0) (hf : monotone f) (inf : injective f)
  (h : v.is_equiv v') :
  (v.map f h₀ hf).is_equiv (v'.map f h₀ hf) :=
λ r s,
calc f (v r) ≤ f (v s) ↔ v r ≤ v s : by rw linear_order_le_iff_of_monotone_injective inf hf
                   ... ↔ v' r ≤ v' s : h r s
                   ... ↔ f (v' r) ≤ f (v' s) : by rw linear_order_le_iff_of_monotone_injective inf hf

/-- `comap` preserves equivalence. -/
lemma comap {S : Type u₃} [ring S] (f : S → R) [is_ring_hom f] (h : v₁.is_equiv v₂) :
  (v₁.comap f).is_equiv (v₂.comap f) :=
λ r s, h (f r) (f s)

lemma val_eq (h : v₁.is_equiv v₂) {r s : R} :
  v₁ r = v₁ s ↔ v₂ r = v₂ s :=
⟨λ H, le_antisymm ((h _ _).1 (le_of_eq H)) ((h _ _).1 (le_of_eq H.symm)),
 λ H, le_antisymm ((h.symm _ _).1 (le_of_eq H)) ((h.symm _ _).1 (le_of_eq H.symm)) ⟩

lemma ne_zero (h : v₁.is_equiv v₂) {r : R} :
  v₁ r ≠ 0 ↔ v₂ r ≠ 0 :=
begin
  have : v₁ r ≠ v₁ 0 ↔ v₂ r ≠ v₂ 0 := not_iff_not_of_iff h.val_eq,
  rwa [v₁.map_zero, v₂.map_zero] at this,
end

end is_equiv -- end of namespace

lemma is_equiv_of_map_strict_mono [ring R] {v : valuation R Γ}
  (f : Γ →* Γ₁) (h₀ : f 0 = 0) (H : strict_mono f) :
  is_equiv (v.map f h₀ (H.monotone)) v :=
λ x y, ⟨H.le_iff_le.mp, λ h, H.monotone h⟩

section trivial -- the trivial valuation
variable [comm_ring R]
variables (S : ideal R) [prime : ideal.is_prime S]
include prime

/-- The trivial Γ-valued valuation associated to a prime ideal S of R. -/
def trivial : valuation R Γ :=
{ to_fun := λ x, if x ∈ S then 0 else 1,
  map_zero' := if_pos S.zero_mem,
  map_one'  := if_neg (assume h, prime.1 (S.eq_top_iff_one.2 h)),
  map_mul'  := λ x y,
    if hx : x ∈ S then by rw [if_pos hx, zero_mul, if_pos (S.mul_mem_right hx)]
    else if hy : y ∈ S then by rw [if_pos hy, mul_zero, if_pos (S.mul_mem_left hy)]
    else have hxy : x * y ∉ S,
    by { assume hxy, replace hxy := prime.mem_or_mem hxy, tauto },
    by rw [if_neg hx, if_neg hy, if_neg hxy, mul_one],
  map_add'  := λ x y, begin
      split_ifs with hxy hx hy _ hx hy;
      try {simp}; try {exact le_refl _},
      { exact hxy (S.add_mem hx hy) }
    end }

end trivial -- end of section

section supp
variables  [comm_ring R]
variables (v : valuation R Γ)

/-- The support of a valuation v : R → {0} ∪ Γ is the ideal of R where v vanishes. -/
def supp : ideal R :=
{ carrier := {x | v x = 0},
  zero := map_zero v,
  add  := λ x y hx hy, or.cases_on (map_add v x y)
    (λ hxy, le_antisymm (hx ▸ hxy) linear_ordered_comm_group_with_zero.zero_le)
    (λ hxy, le_antisymm (hy ▸ hxy) linear_ordered_comm_group_with_zero.zero_le),
  smul  := λ c x hx, calc v (c * x)
                        = v c * v x : map_mul v c x
                    ... = v c * 0 : congr_arg _ hx
                    ... = 0 : mul_zero _ }

@[simp] lemma mem_supp_iff (x : R) : x ∈ supp v ↔ v x = 0 := iff.rfl
-- @[simp] lemma mem_supp_iff' (x : R) : x ∈ (supp v : set R) ↔ v x = 0 := iff.rfl

/-- The support of a valuation is a prime ideal. -/
instance : ideal.is_prime (supp v) :=
⟨λ (h : v.supp = ⊤), one_ne_zero $ show (1 : Γ) = 0,
from calc 1 = v 1 : v.map_one.symm
        ... = 0   : show (1:R) ∈ supp v, by rw h; trivial,
 λ x y hxy, begin
    show v x = 0 ∨ v y = 0,
    change v (x * y) = 0 at hxy,
    rw [v.map_mul x y] at hxy,
    exact group_with_zero.mul_eq_zero _ _ hxy
  end⟩

-- lemma v_nonzero_of_not_in_supp (a : R) (h : a ∉ supp v) : v a ≠ 0 := λ h2, h h2

-- /-- A Γ-valued variant v_to_Γ of a valuation v, with v_to_Γ(x)=1 if v(x)=0. -/
-- def v_to_Γ (a : R) : Γ :=
-- option.rec_on (v a) 1 id

-- variable {v}

-- lemma v_to_Γ_is_v {a : R} (h : a ∉ supp v) : v a = ↑(v_to_Γ v a) :=
-- begin
--   destruct (v a),
--   { intro h2,
--     exfalso,
--     apply v_nonzero_of_not_in_supp v a h,
--     exact h2
--   },
--   { intros g hg,
--     unfold v_to_Γ,
--     rw hg, refl,
--   }
-- end

/-- v(a)=v(a+s) if s ∈ supp(v). -/
lemma val_add_supp (a s : R) (h : s ∈ supp v) : v (a + s) = v a :=
begin
  have aux : ∀ a s, v s = 0 → v (a + s) ≤ v a,
  { intros a' s' h', cases v.map_add a' s' with H H; simp * at * },
  apply le_antisymm (aux a s h),
  calc v a = v (a + s + -s) : by simp
       ... ≤ v (a + s)      : aux (a + s) (-s) (by rwa ←ideal.neg_mem_iff at h)
end

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
definition on_quot_val {J : ideal R} (hJ : J ≤ supp v) :
  J.quotient → Γ :=
λ q, quotient.lift_on' q v $ λ a b h,
calc v a = v (b + (a - b)) : by simp
     ... = v b             : v.val_add_supp b (a - b) (hJ h)

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
definition on_quot {J : ideal R} (hJ : J ≤ supp v) :
  valuation J.quotient Γ :=
{ to_fun := v.on_quot_val hJ,
  map_zero' := v.map_zero,
  map_one'  := v.map_one,
  map_mul'  := λ xbar ybar, quotient.ind₂' v.map_mul xbar ybar,
  map_add'  := λ xbar ybar, quotient.ind₂' v.map_add xbar ybar }

@[simp] lemma on_quot_comap_eq {J : ideal R} (hJ : J ≤ supp v) :
  (v.on_quot hJ).comap (ideal.quotient.mk J) = v :=
ext $ λ r,
begin
  refine @quotient.lift_on_beta _ _ (J.quotient_rel) v (λ a b h, _) _,
  calc v a = v (b + (a - b)) : by simp
       ... = v b             : v.val_add_supp b (a - b) (hJ h)
end

end supp -- end of section

section supp_comm
variable [comm_ring R]
variables (v : valuation R Γ)

lemma comap_supp {S : Type u₁} [comm_ring S] (f : S → R) [is_ring_hom f] :
  supp (v.comap f) = ideal.comap f v.supp :=
ideal.ext $ λ x,
begin
  rw [mem_supp_iff, ideal.mem_comap, mem_supp_iff],
  refl,
end

lemma self_le_supp_comap (J : ideal R) (v : valuation (quotient J) Γ) :
  J ≤ (v.comap (ideal.quotient.mk J)).supp :=
by rw [comap_supp, ← ideal.map_le_iff_le_comap]; simp

@[simp] lemma comap_on_quot_eq (J : ideal R) (v : valuation J.quotient Γ) :
  (v.comap (ideal.quotient.mk J)).on_quot (v.self_le_supp_comap J) = v :=
ext $ by { rintro ⟨x⟩, refl }

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
lemma supp_quot {J : ideal R} (hJ : J ≤ supp v) :
supp (v.on_quot hJ) = (supp v).map (ideal.quotient.mk J) :=
begin
  apply le_antisymm,
  { rintro ⟨x⟩ hx,
    apply ideal.subset_span,
    exact ⟨x, hx, rfl⟩ },
  { rw ideal.map_le_iff_le_comap,
    intros x hx, exact hx }
end

lemma supp_quot_supp : supp (v.on_quot (le_refl _)) = 0 :=
by rw supp_quot; exact ideal.map_quotient_self _

lemma quot_preorder_comap {J : ideal R} (hJ : J ≤ supp v) :
preorder.lift (ideal.quotient.mk J) (v.on_quot hJ).to_preorder = v.to_preorder :=
preorder.ext $ λ x y, iff.rfl

end supp_comm -- end of section

end valuation
