import algebra.group_power
import ring_theory.ideal_operations
import ring_theory.localization
import ring_theory.subring

import for_mathlib.rings
import for_mathlib.linear_ordered_comm_group
import for_mathlib.equiv

/- valuations.basic

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following Wedhorn's unpublished notes on adic spaces.

The definition of a valuation is Definition 1.22 of Wedhorn. `valuation R Γ`
is the type of valuations R → Γ ∪ {0}, with a coercion to the underlying
function. If v is a valuation from R to Γ ∪ {0} then the induced group
homomorphism units(R) → Γ is called `unit_map v`.

The equivalence "relation" `is_equiv v₁ v₂ : Prop` is not strictly speaking a
relation, because v₁ : valuation R Γ₁ and v₂ : valuation R Γ₂ might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as Γ varies) on a ring R is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense.

The trivial valuation associated to a prime ideal P is
`trivial P : valuation R Γ`.

The support of a valuation v : valuation R Γ is `supp v`. The induced valuation
on R / J = `ideal.quotient J` if `h : J ⊆ supp v` is `on_quot v h`.

If v is a valuation on an integral domain R and `hv : supp v = 0`, then
`on_frac v hv` is the extension of v to fraction_ring R, the field of
fractions of R.

`valuation_field v`, `valuation_ring v`, `max_ideal v` and `residue_field v`
are the valuation field, valuation ring, maximal ideal and residue field
of v. See Definition 1.26 of Wedhorn.
-/

local attribute [instance] classical.prop_decidable
noncomputable theory

/- Seems to be in mathlib already
-- Some counter-Kenny trick, no need to read
def classical.decidable_linear_order {α : Type*} [linear_order α] : decidable_linear_order α :=
{ decidable_le := by apply_instance,
  decidable_eq := by apply_instance,
  decidable_lt := by apply_instance, ..‹linear_order α› }
-/

local attribute [instance, priority 0] classical.decidable_linear_order

open function with_zero ideal localization

universes u u₀ u₁ u₂ u₃ -- v is used for valuations

variables {Γ : Type u} [linear_ordered_comm_group Γ]
variables {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]
variables {Γ₃ : Type u₃} [linear_ordered_comm_group Γ₃]

variables {R : Type u₀} -- This will be a ring, assumed commutative in some sections


-- Valuations on a ring with values in {0} ∪ Γ
class valuation.is_valuation [ring R] (v : R → with_zero Γ) : Prop :=
(map_zero : v 0 = 0)
(map_one  : v 1 = 1)
(map_mul  : ∀ x y, v (x * y) = v x * v y)
(map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y)

/-- Γ-valued valuations on R -/
def valuation (R : Type u₀) [ring R] (Γ : Type u) [linear_ordered_comm_group Γ] :=
{ v : R → with_zero Γ // valuation.is_valuation v }

namespace valuation

section
variables [ring R]

-- A valuation is coerced to the underlying function R → {0} ∪ Γ
instance (R : Type u₀) [ring R] (Γ : Type u) [linear_ordered_comm_group Γ] :
has_coe_to_fun (valuation R Γ) := { F := λ _, R → with_zero Γ, coe := subtype.val}

@[extensionality] lemma ext {Γ : Type u} [linear_ordered_comm_group Γ] (v₁ v₂ : valuation R Γ) :
  v₁ = v₂ ↔ ∀ r, v₁ r = v₂ r :=
subtype.ext.trans ⟨λ h r, congr h rfl, funext⟩

variables (v : valuation R Γ) {x y z : R}

instance : is_valuation v := v.property

@[simp] lemma map_zero : v 0 = 0 := v.property.map_zero
@[simp] lemma map_one  : v 1 = 1 := v.property.map_one
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := v.property.map_mul
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y := v.property.map_add

lemma map_one_ne_zero : v 1 ≠ 0 := by rw map_one; simp

lemma map_add_le_max (x y) : v (x + y) ≤ max (v x) (v y) :=
begin
  cases map_add v x y with h,
  apply le_max_left_of_le h,
  apply le_max_right_of_le h,
end

-- not an instance, because more than one v on a given R
/-- a valuation gives a preorder on the underlying ring-/
def to_preorder : preorder R := preorder.lift v (by apply_instance)

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

-- As far as Patrick can see, this is the useful version of valuation.map_unit
lemma unit_is_some (x : units R) : ∃ γ : Γ, v x = γ :=
begin
  have h1 := v.map_mul x.val x.inv,
  rw [x.val_inv, valuation.map_one] at h1,
  exact with_zero.eq_coe_of_mul_eq_coe_left h1.symm
end

lemma unit_is_not_none (x : units R) : v x ≠ 0 :=
begin
  cases unit_is_some v x with γ Hγ,
  rw Hγ,
  apply option.no_confusion,
end

lemma unit_is_some' {Γ : Type u} [_inst_1 : linear_ordered_comm_group Γ] {R : Type u₀} [comm_ring R]
  (v : valuation R Γ) {x : R} (h : ∃ y : R, x * y = 1) : ∃ γ : Γ, v x = γ :=
begin
  cases h with y hy,
  let x' : units R := units.mk x y hy (mul_comm x y ▸ hy),
  exact unit_is_some v x'
end

lemma map_inv (x : units R) : v x⁻¹.val = (v x)⁻¹ :=
begin
  have := congr_arg v x.val_inv,
  rw [v.map_one, map_mul] at this,
  exact with_zero.eq_inv_of_mul_eq_one_right this,
end

lemma map_unit' (x : units R) : (v x).is_some := map_unit v x.val_inv

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

@[simp]
lemma coe_unit_map (x : units R)  : ↑(v.unit_map x) = v x :=
by rw ← valuation.unit_map_eq ; refl

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

section

variables {v₁ : R → with_zero Γ₁} {v₂ : R → with_zero Γ₂}
variables {ψ : Γ₁ → Γ₂}
variables (H12 : ∀ r, with_zero.map ψ (v₁ r) = v₂ r)
variables (Hle : ∀ g h : Γ₁, g ≤ h ↔ ψ g ≤ ψ h)
-- This include statement means that we have an underlying assumption
-- that ψ : Γ₁ → Γ₂ is order-preserving, and that v₁ and v₂ are functions with ψ ∘ v₁ = v₂.
include H12 Hle

theorem le_of_le (r s : R) : v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s :=
by { rw ←H12 r, rw ←H12 s, exact with_zero.map_le Hle _ _ }

-- Restriction of a Γ₂-valued valuation to a subgroup Γ₁ is still a valuation
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
    apply (is_valuation.map_add v₂ r s).imp _ _;
    erw [with_zero.map_le Hle, ←H12, ←H12];
    exact id
  end }

end -- section

/-- f : S → R induces map valuation R Γ → valuation S Γ -/
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


-- Definition of equivalence relation on valuations
def is_equiv (v₁ : valuation R Γ₁) (v₂ : valuation R Γ₂) : Prop :=
∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s
end

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

end is_equiv

lemma is_equiv_of_map_of_strict_mono [ring R] {v : valuation R Γ}
(f : Γ → Γ₁) [is_group_hom f] (H : strict_mono f) :
  is_equiv (v.map f (H.monotone)) v :=
λ x y, ⟨(with_zero.map_strict_mono H).le_iff_le.mp, λ h, with_zero.map_monotone H.monotone h⟩

section trivial
variable [comm_ring R]
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
variables  [comm_ring R]
variables (v : valuation R Γ)

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

lemma v_nonzero_of_not_in_supp (a : R) (h : a ∉ supp v) : v a ≠ 0 := λ h2, h h2

-- group version of v
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
  apply le_antisymm (val_add_supp_aux a s h),
  convert val_add_supp_aux (a + s) (-s) _, simp,
  rwa ←ideal.neg_mem_iff at h,
end

variable (v)

-- Function corresponding to extension of a valuation on R to a valuation on R / J if J is in the support -/
definition on_quot_val {J : ideal R} (hJ : J ≤ supp v) :
  J.quotient → with_zero Γ :=
λ q, quotient.lift_on' q v $ λ a b h,
begin
  have hsupp : a - b ∈ supp v := hJ h,
  convert val_add_supp b (a - b) hsupp,
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
    by convert val_add_supp b (a - b) hsupp; simp) _
end supp

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

lemma quot_supp_zero : supp (v.on_quot (le_refl _)) = 0 :=
by rw supp_quot_supp; exact ideal.map_quotient_self _

lemma quot_preorder_comap {J : ideal R} (hJ : J ≤ supp v) :
preorder.lift (ideal.quotient.mk J) (v.on_quot hJ).to_preorder = v.to_preorder :=
preorder.ext $ λ x y, iff.rfl

end supp_comm



section fraction_ring

variables [integral_domain R] -- integral domain is abreviated ID in the following
variables (v : valuation R Γ)

-- function corresponding to extension of valuation on ID with support 0
-- to valuation on field of fractions
definition on_frac_val (hv : supp v = 0) : fraction_ring R → with_zero Γ :=
quotient.lift (λ rs, v rs.1 / v rs.2.1 : R × non_zero_divisors R → with_zero Γ)
begin
  rintro ⟨r, s, hs⟩ ⟨t, u, hu⟩ ⟨w, hw, h⟩,
  change v r / v s = v t / v u,
  change (s * t - (u * r)) * w = 0 at h,
  rw fraction_ring.mem_non_zero_divisors_iff_ne_zero at hs hu hw,
  have hvs : v s ≠ 0 := λ H, hs ((submodule.mem_bot R).mp (lattice.eq_bot_iff.1 hv H)),
  have hvu : v u ≠ 0 := λ H, hu ((submodule.mem_bot R).mp (lattice.eq_bot_iff.1 hv H)),
  have hvw : v w ≠ 0 := λ H, hw ((submodule.mem_bot R).mp (lattice.eq_bot_iff.1 hv H)),
  rw [with_zero.div_eq_div hvs hvu],
  rw [sub_mul, sub_eq_zero] at h, replace h := congr_arg v h,
  iterate 4 { rw map_mul at h },
  cases v w with w hvw,
  { exact false.elim (hvw rfl), },
  rw mul_comm,
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
  (v.on_frac hv).comap of = v :=
subtype.ext.mpr $ funext $ λ r, show v r / v 1 = v r, by simp

lemma on_frac_comap_eq' (hv : supp v = 0) (r : R) :
  ((v.on_frac hv).comap of : valuation R Γ) r = v r := by rw on_frac_comap_eq

@[simp] lemma comap_on_frac_eq (v : valuation (fraction_ring R) Γ) :
  (v.comap of).on_frac
  (by {rw [comap_supp, ideal.zero_eq_bot, (supp v).eq_bot_of_prime],
    apply ideal.comap_bot_of_inj, apply fraction_ring.of.injective })
  = v :=
subtype.ext.mpr $ funext $
begin
  rintro ⟨x⟩,
  dsimp [on_frac, on_frac_val, comap, function.comp],
  erw quotient.lift_beta,
  change v (x.1) / v (x.2.val) = _,
  rw with_zero.div_eq_iff_mul_eq,
  { erw ← v.map_mul,
    apply congr_arg,
    change ⟦_⟧ = ⟦_⟧,
    apply quotient.sound,
    use 1, use is_submonoid.one_mem _,
    show (↑(x.snd) * 1 * x.fst + -(1 * (x.fst * (x.snd).val))) * 1 = 0,
    rw [mul_one, mul_one, one_mul, mul_comm],
    exact sub_self _},
  intro h,
  rw [← mem_supp_iff, (supp v).eq_bot_of_prime, submodule.mem_bot] at h,
  replace h := fraction_ring.eq_zero_of _ h,
  refine fraction_ring.mem_non_zero_divisors_iff_ne_zero.mp _ h,
  exact x.2.2
end

lemma frac_preorder_comap (hv : supp v = 0) :
  preorder.lift (localization.of) (v.on_frac hv).to_preorder = v.to_preorder :=
preorder.ext $ λ x y, begin show (v.on_frac hv) x ≤ (v.on_frac hv) y ↔ v x ≤ v y,
rw [←on_frac_comap_eq' v hv, ←on_frac_comap_eq' v hv], exact iff.rfl end

end fraction_ring

section valuation_field

variables [comm_ring R]
variables (v : valuation R Γ)

definition valuation_ID := (supp v).quotient

instance valuation.integral_domain' : integral_domain (valuation_ID v) :=
by delta valuation_ID; apply_instance

instance : preorder (valuation_ID v) := (v.on_quot (le_refl _)).to_preorder

def valuation_ID_mk : R → valuation_ID v := ideal.quotient.mk (supp v)

-- need that it's a ring hom, need that its kernel is whatever

instance : is_ring_hom (v.valuation_ID_mk) := by unfold valuation_ID_mk; apply_instance

lemma valuation_ID_mk_ker (r : R) : v.valuation_ID_mk r = 0 ↔ r ∈ supp v :=
ideal.quotient.eq_zero_iff_mem

definition valuation_field := localization.fraction_ring (valuation_ID v)

instance : discrete_field (valuation_field v) := by delta valuation_field; apply_instance

def valuation_field_mk (r : R) : valuation_field v := localization.of (v.valuation_ID_mk r)

instance to_valuation_field.is_ring_hom : is_ring_hom (valuation_field_mk v) :=
by delta valuation_field_mk; apply_instance

lemma valuation_field_mk_ker (r : R) : v.valuation_field_mk r = 0 ↔ r ∈ supp v :=
⟨λ h, (v.valuation_ID_mk_ker r).1 $ localization.fraction_ring.eq_zero_of _ h,
 λ h, show localization.of _ = 0, by rw (v.valuation_ID_mk_ker r).2 h; apply is_ring_hom.map_zero⟩

lemma valuation_field_mk_ne_zero (r : R) (hr : v r ≠ 0) : valuation_field_mk v r ≠ 0 :=
λ h, hr ((valuation_field_mk_ker v r).1 h)

instance valuation.valfield_preorder : preorder (valuation_field v) :=
  ((v.on_quot (le_refl _)).on_frac $ quot_supp_zero v).to_preorder

def units_valfield_mk (r : R) (h : r ∉ supp v) : units (valuation_field v) :=
⟨v.valuation_field_mk r,
 (v.valuation_field_mk r)⁻¹,
 mul_inv_cancel (λ h2, h $ ideal.quotient.eq_zero_iff_mem.1 $
   localization.fraction_ring.eq_zero_of _ h2),
 inv_mul_cancel (λ h2, h $ ideal.quotient.eq_zero_iff_mem.1 $
   localization.fraction_ring.eq_zero_of _ h2)⟩

instance valuation.units_valfield_preorder :
  preorder (units (valuation_field v)) := preorder.lift (λ u, u.val) (by apply_instance)

-- on_frac_quot_comap_eq needs more class.instance_max_depth to compile if
-- this instance is not explicitly given as a hint
instance : is_submonoid (localization.non_zero_divisors (ideal.quotient (supp v))) :=
by apply_instance

-- @[simp] lemma on_frac_quot_comap_eq :
--   ((v.on_quot (le_refl _)).on_frac $ quot_supp_zero v).comap
--   (@localization.of v.supp.quotient _ _ (by {  }) ∘ (ideal.quotient.mk v.supp))
--    = v :=
-- by rw [comap_comp, on_frac_comap_eq, on_quot_comap_eq]

definition on_valuation_field : valuation (valuation_field v) Γ :=
on_frac (v.on_quot (set.subset.refl _))
begin
  rw [supp_quot_supp],
  rw zero_eq_bot,
  apply ideal.map_quotient_self,
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

set_option class.instance_max_depth 40

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

set_option class.instance_max_depth 32

definition residue_field := (max_ideal v).quotient

instance residue_field.discrete_field : discrete_field (residue_field v) := ideal.quotient.field _
end valuation_field
end valuation
