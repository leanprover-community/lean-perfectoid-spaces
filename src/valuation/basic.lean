import algebra.group_power
import ring_theory.ideal_operations
import ring_theory.subring

import for_mathlib.rings
import for_mathlib.linear_ordered_comm_group
import for_mathlib.equiv

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

open function with_zero ideal

universes u u₀ u₁ u₂ u₃ -- v is used for valuations

variables {Γ : Type u} [linear_ordered_comm_group Γ]
variables {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]
variables {Γ₃ : Type u₃} [linear_ordered_comm_group Γ₃]

variables {R : Type u₀} -- This will be a ring, assumed commutative in some sections

/-- Predicate for valuations on a ring R with values in {0} ∪ Γ. -/
structure valuation.is_valuation [ring R] (v : R → with_zero Γ) : Prop :=
(map_zero : v 0 = 0)
(map_one  : v 1 = 1)
(map_mul  : ∀ x y, v (x * y) = v x * v y)
(map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y)

/-- The type of ({0} ∪ Γ)-valued valuations on R. -/
def valuation (R : Type u₀) [ring R] (Γ : Type u) [linear_ordered_comm_group Γ] :=
{ v : R → with_zero Γ // valuation.is_valuation v }

namespace valuation

section basic
variables [ring R]

/-- A valuation is coerced to the underlying function R → {0} ∪ Γ. -/
instance (R : Type u₀) [ring R] (Γ : Type u) [linear_ordered_comm_group Γ] :
has_coe_to_fun (valuation R Γ) := { F := λ _, R → with_zero Γ, coe := subtype.val}

lemma ext_iff {Γ : Type u} [linear_ordered_comm_group Γ] {v₁ v₂ : valuation R Γ} :
  v₁ = v₂ ↔ ∀ r, v₁ r = v₂ r :=
subtype.ext.trans ⟨λ h r, congr h rfl, funext⟩

@[extensionality] lemma ext {Γ : Type u} [linear_ordered_comm_group Γ] {v₁ v₂ : valuation R Γ} :
  (∀ r, v₁ r = v₂ r) → v₁ = v₂ :=
valuation.ext_iff.mpr

variables (v : valuation R Γ) {x y z : R}

@[simp] lemma map_zero : v 0 = 0 := v.property.map_zero
@[simp] lemma map_one  : v 1 = 1 := v.property.map_one
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := v.property.map_mul
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y := v.property.map_add

lemma map_add_le_max (x y) : v (x + y) ≤ max (v x) (v y) :=
begin
  cases map_add v x y with h,
  apply le_max_left_of_le h,
  apply le_max_right_of_le h,
end

-- The following definition is not an instance, because we have more than one v on a given R.
/-- A valuation gives a preorder on the underlying ring. -/
def to_preorder : preorder R := preorder.lift v (by apply_instance)

/-- If x ∈ R is a unit then v x is non-zero. -/
theorem map_unit (h : x * y = 1) : (v x).is_some :=
begin
  have h1 := v.map_mul x y,
  rw [h, map_one v] at h1,
  cases (v x),
  { exfalso,
    exact option.no_confusion h1 },
  { constructor }
end

/-- If x is a unit of R then there exists γ∈Γ with v(x)=γ. -/
lemma unit_is_some (x : units R) : ∃ γ : Γ, v x = γ :=
begin
  have h1 := v.map_mul x.val x.inv,
  rw [x.val_inv, valuation.map_one] at h1,
  exact with_zero.eq_coe_of_mul_eq_coe_left h1.symm
end

/-- If x is a unit of R then v x is non-zero. -/
lemma map_unit_ne_zero (x : units R) : v x ≠ 0 :=
begin
  cases unit_is_some v x with γ Hγ,
  rw Hγ,
  apply option.no_confusion,
end

/-- If v is a valuation on a division ring then v(x)=0 iff x=0. -/
lemma zero_iff {Γ : Type u} [linear_ordered_comm_group Γ] {K : Type u₀} [division_ring K]
  (v : valuation K Γ) {x : K} : v x = 0 ↔ x = 0 :=
begin
  split ; intro h,
  { by_contradiction h',
    -- TODO: replace next two lines by `obtain` after bump
    cases valuation.unit_is_some v (units.mk0 x h') with γ h'',
    change v x = γ at h'',
    rw h'' at h,
    exact with_zero.coe_ne_zero h },
  { exact h.symm ▸ v.map_zero },
end

lemma map_inv {Γ : Type u} [linear_ordered_comm_group Γ] {K : Type u₀} [division_ring K]
  (v : valuation K Γ) {x : K} (h : x ≠ 0) : v x⁻¹ = (v x)⁻¹ :=
begin
  apply with_zero.eq_inv_of_mul_eq_one_right,
  rw [← v.map_mul, mul_inv_cancel h, v.map_one]
end

lemma ne_zero_iff {Γ : Type u} [linear_ordered_comm_group Γ] {K : Type u₀} [division_ring K]
  (v : valuation K Γ) {x : K} : v x ≠ 0 ↔ x ≠ 0 :=
not_iff_not_of_iff v.zero_iff

lemma coe_of_ne_zero {Γ : Type u} [linear_ordered_comm_group Γ] {K : Type u₀} [division_ring K]
  (v : valuation K Γ) {x : K} (h : x ≠ 0) : ∃ γ : Γ, v x = γ :=
by rwa [← v.ne_zero_iff, with_zero.ne_zero_iff_exists] at h

lemma map_units_inv (x : units R) : v x⁻¹.val = (v x)⁻¹ :=
begin
  have := congr_arg v x.val_inv,
  rw [v.map_one, map_mul] at this,
  exact with_zero.eq_inv_of_mul_eq_one_right this,
end

lemma map_unit' (x : units R) : (v x).is_some := map_unit v x.val_inv

/-- `unit_map v` is the map R^× → Γ associated to a valuation v : R → {0} ∪ Γ.-/
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

lemma unit_map.ext (x z : units R) (H : v (z.val) = v (x.val)) :
  valuation.unit_map v z = valuation.unit_map v x :=
by rwa [←option.some_inj, valuation.unit_map_eq, valuation.unit_map_eq]

@[simp] lemma coe_unit_map (x : units R)  : ↑(v.unit_map x) = v x :=
by rw ← valuation.unit_map_eq ; refl

/-- The unit_map associated to a valuation is a group homomorphism. -/
instance unit_map.is_group_hom : is_group_hom (unit_map v) :=
is_group_hom.mk' $
λ a b, option.some.inj $
  show _ = (some _ * some _ : with_zero Γ),
  by simp

@[simp] theorem map_neg_one : v (-1) = 1 :=
begin
  change v (-1 : units R) = 1,
  rw ← unit_map_eq,
  congr' 1,
  apply linear_ordered_structure.eq_one_of_pow_eq_one (_ : _ ^ 2 = _),
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

@[simp] theorem eq_zero_iff_le_zero {r : R} : v r = 0 ↔ v r ≤ v 0 :=
v.map_zero.symm ▸ with_zero.le_zero_iff_eq_zero.symm

section change_of_group

variables {v₁ : R → with_zero Γ₁} {v₂ : R → with_zero Γ₂}
variables {ψ : Γ₁ → Γ₂}
variables (H12 : ∀ r, with_zero.map ψ (v₁ r) = v₂ r)
variables (Hle : ∀ g h : Γ₁, g ≤ h ↔ ψ g ≤ ψ h)
-- This include statement means that we have an underlying assumption
-- that ψ : Γ₁ → Γ₂ is order-preserving, and that v₁ and v₂ are functions with ψ ∘ v₁ = v₂.
include H12 Hle

theorem le_of_le (r s : R) : v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s :=
by { rw ←H12 r, rw ←H12 s, exact with_zero.map_le Hle _ _ }

/-- Restriction of a Γ₂-valued valuation to a subgroup Γ₁ is still a valuation. -/
theorem valuation_of_valuation [is_group_hom ψ] (Hiψ : function.injective ψ) (H : is_valuation v₂) :
is_valuation v₁ :=
{ map_zero := with_zero.injective_map Hiψ $
    by erw [H12, H.map_zero, ← with_zero.map_zero],
  map_one := with_zero.injective_map Hiψ $
    by erw [H12, H.map_one, with_zero.map_coe, is_group_hom.map_one ψ]; refl,
  map_mul := λ r s, with_zero.injective_map Hiψ $
    by rw [H12, H.map_mul, ←H12 r, ←H12 s]; exact (with_zero.map_mul _ _ _).symm,
  map_add := λ r s,
  begin
    apply (H.map_add r s).imp _ _;
    erw [with_zero.map_le Hle, ←H12, ←H12];
    exact id
  end }

end change_of_group -- section

/-- A ring homomorphism S → R induces a map valuation R Γ → valuation S Γ -/
def comap {S : Type u₁} [ring S] (f : S → R) [is_ring_hom f] : valuation S Γ :=
{ val := v ∘ f,
  property := by constructor;
    simp [is_ring_hom.map_zero f, is_ring_hom.map_one f,
      is_ring_hom.map_mul f, is_ring_hom.map_add f] }

lemma comap_id : v.comap (id : R → R) = v := subtype.eq rfl

lemma comap_comp {S₁ : Type u₁} [ring S₁] {S₂ : Type u₂} [ring S₂]
(f : S₁ → S₂) [is_ring_hom f] (g : S₂ → R) [is_ring_hom g] :
  v.comap (g ∘ f) = (v.comap g).comap f :=
subtype.ext.mpr $ rfl

/-- A ≤-preserving group homomorphism Γ → Γ₁ induces a map valuation R Γ → valuation R Γ₁. -/
def map {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
  (f : Γ → Γ₁) [is_group_hom f] (hf : monotone f) :
valuation R Γ₁ :=
{ val := with_zero.map f ∘ v,
  property :=
  { map_zero := by simp [with_zero.map_zero],
    map_one :=
    begin
      show with_zero.map f (_) = 1,
      erw [v.map_one, with_zero.map_coe, is_group_hom.map_one f],
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

lemma map {v' : valuation R Γ} (f : Γ → Γ₁) [is_group_hom f] (inf : injective f) (hf : monotone f)
  (h : v.is_equiv v') : (map v f hf).is_equiv (map v' f hf) := λ r s, begin
  show (with_zero.map f) (v r) ≤ (with_zero.map f) (v s) ↔
    (with_zero.map f) (v' r) ≤ (with_zero.map f) (v' s),
  rw ←linear_order_le_iff_of_monotone_injective (with_zero.injective_map inf) (with_zero.map_monotone hf),
  rw ←linear_order_le_iff_of_monotone_injective (with_zero.injective_map inf) (with_zero.map_monotone hf),
  apply h,
end

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

lemma is_equiv_of_map_of_strict_mono [ring R] {v : valuation R Γ}
(f : Γ → Γ₁) [is_group_hom f] (H : strict_mono f) :
  is_equiv (v.map f (H.monotone)) v :=
λ x y, ⟨(with_zero.map_strict_mono H).le_iff_le.mp, λ h, with_zero.map_monotone H.monotone h⟩

section trivial -- the trivial valuation
variable [comm_ring R]
variables (S : ideal R) [prime : ideal.is_prime S]
include prime

/-- The trivial Γ-valued valuation associated to a prime ideal S of R. -/
def trivial : valuation R Γ :=
{ val := λ x, if x ∈ S then 0 else 1,
  property :=
  { map_zero := if_pos S.zero_mem,
    map_one  := if_neg (assume h, prime.1 (S.eq_top_iff_one.2 h)),
    map_mul  := λ x y,
      if hx : x ∈ S then by rw [if_pos hx, zero_mul, if_pos (S.mul_mem_right hx)]
      else if hy : y ∈ S then by rw [if_pos hy, mul_zero, if_pos (S.mul_mem_left hy)]
      else have hxy : x * y ∉ S,
      by { assume hxy, replace hxy := prime.mem_or_mem hxy, tauto },
      by rw [if_neg hx, if_neg hy, if_neg hxy, mul_one],
    map_add  := λ x y, begin
        split_ifs with hxy hx hy _ hx hy;
        try {simp}; try {exact le_refl _},
        { exact hxy (S.add_mem hx hy) }
      end } }

end trivial -- end of section

section supp
variables  [comm_ring R]
variables (v : valuation R Γ)

/-- The support of a valuation v : R → {0} ∪ Γ is the ideal of R where v vanishes. -/
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

/-- The support of a valuation is a prime ideal. -/
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

lemma v_nonzero_of_not_in_supp (a : R) (h : a ∉ supp v) : v a ≠ 0 := λ h2, h h2

/-- A Γ-valued variant v_to_Γ of a valuation v, with v_to_Γ(x)=1 if v(x)=0. -/
def v_to_Γ (a : R) : Γ :=
option.rec_on (v a) 1 id

variable {v}

lemma v_to_Γ_is_v {a : R} (h : a ∉ supp v) : v a = ↑(v_to_Γ v a) :=
begin
  destruct (v a),
  { intro h2,
    exfalso,
    apply v_nonzero_of_not_in_supp v a h,
    exact h2
  },
  { intros g hg,
    unfold v_to_Γ,
    rw hg, refl,
  }
end

-- just an auxiliary lemma.
lemma val_add_supp_aux (a s : R) (h : v s = 0) : v (a + s) ≤ v a :=
begin
  cases map_add v a s with H H, exact H,
  change v s = 0 at h,
  rw h at H,
  exact le_trans H with_zero.zero_le
end

/-- v(a)=v(a+s) if s ∈ supp(v). -/
lemma val_add_supp (a s : R) (h : s ∈ supp v) : v (a + s) = v a :=
begin
  apply le_antisymm (val_add_supp_aux a s h),
  convert val_add_supp_aux (a + s) (-s) _, simp,
  rwa ←ideal.neg_mem_iff at h,
end

variable (v)

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
definition on_quot_val {J : ideal R} (hJ : J ≤ supp v) :
  J.quotient → with_zero Γ :=
λ q, quotient.lift_on' q v $ λ a b h,
begin
  have hsupp : a - b ∈ supp v := hJ h,
  convert val_add_supp b (a - b) hsupp,
  simp,
end

variable {v}

/-- Proof that `on_quot_val hJ` is a valuation. -/
lemma on_quot_val.is_valuation {J : ideal R} (hJ : J ≤ supp v) :
is_valuation (on_quot_val v hJ) :=
{ map_zero := v.map_zero,
  map_one  := v.map_one,
  map_mul  := λ xbar ybar, quotient.ind₂' v.map_mul xbar ybar,
  map_add  := λ xbar ybar, quotient.ind₂' v.map_add xbar ybar }

variable (v)

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
definition on_quot {J : ideal R} (hJ : J ≤ supp v) :
  valuation J.quotient Γ :=
{ val := v.on_quot_val hJ,
  property := on_quot_val.is_valuation hJ }

@[simp] lemma on_quot_comap_eq {J : ideal R} (hJ : J ≤ supp v) :
  (v.on_quot hJ).comap (ideal.quotient.mk J) = v :=
subtype.ext.mpr $ funext $
  λ r, @quotient.lift_on_beta _ _ (J.quotient_rel) v
  (λ a b h, have hsupp : a - b ∈ supp v := hJ h,
    by convert val_add_supp b (a - b) hsupp; simp) _

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

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
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

lemma quot_supp_zero : supp (v.on_quot (le_refl _)) = 0 :=
by rw supp_quot_supp; exact ideal.map_quotient_self _

lemma quot_preorder_comap {J : ideal R} (hJ : J ≤ supp v) :
preorder.lift (ideal.quotient.mk J) (v.on_quot hJ).to_preorder = v.to_preorder :=
preorder.ext $ λ x y, iff.rfl

end supp_comm -- end of section

end valuation
