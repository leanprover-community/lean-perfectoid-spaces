import for_mathlib.quotient_group

import valuation.localization

/-!
# The canonical valuation

The purpose of this file is to define a “canonical” valuation equivalent to
a given valuation. The whole raison d'etre for this is that there are set-theoretic
issues with the equivalence “relation” on valuations, because the target group Γ
can be arbitrary.

## Idea

The main idea is this. If v : R → Γ₀ is an arbitrary valuation,
then v extends to a valuation on K = Frac(R/supp(v)) and hence to a monoid
homomorphism K^* → units Γ₀, whose kernel is A^*, the units in the valuation ring
(or equivalently the things in K^* of norm at most 1). This embeds K^*/A^*
into Γ₀ and hence gives K^*/A^* the structure of a linearly ordered commutative group.
There is an induced map R → (K^*/A^*), and we call this the
_canonical valuation_ associated to v; this valuation is equivalent to v.
A technical advantage that this valuation has from the point of view
of Lean's type theory is that if R is in universe u₁ and Γ₀ in universe u₂,
then v : valuation R Γ₀ will be in universe `max u₁ u₂` but the canonical
valuation will just be in universe u₁. In particular, if v and v' are equivalent
then their associated canonical valuations are isomorphic and furthermore in the
same universe.

## Implementation details

All of the below names are in the `valuation` namespace.

The canonical valuation takes values in `value_monoid v`. Technically
this is not defined exactly in the way explained above.
So `value_monoid v` is not defined as `with_zero (K^* / A^*)`.
Instead, we take the equivalence relation on K^* given by A^*,
and extend it in the obvious way to K. The resulting quotient is naturally a monoid,
with an order and a zero element. Indeed, it is a linear_ordered_comm_group_with_zero.
Its unit group is canonically isomorphic to K^*/A^*. (Note that it is also
isomorphic to the subgroup of Γ₀ which Wedhorn calls the value group in [Wedhorn; 1.22]).

`value_monoid.to_Γ₀` is the monoid homomorphism to Γ₀.
`canonical_valuation v` is the canonical valuation.
`canonical_valuation.to_Γ₀ v` is the lemma that says that we can
recover v from `canonical_valuation v` using the monoid homomorphism
from (value_monoid v) to Γ₀.

-- TODO -- rewrite this when I've remembered what we proved.
We then prove some of Proposition-and-Definition 1.27 of Wedhorn,
where we note that we used (iii) for the definition, and
we're now using a different definition to Wedhorn for the value group
(because it's isomorphic so no mathematician will care, and
it's easier for us because it's in a smaller universe).

-/

local attribute [instance] classical.prop_decidable
local attribute [instance, priority 0] classical.decidable_linear_order
noncomputable theory

universes u u₀ u₁ u₂ u₃

open linear_ordered_structure

variables {R : Type u₀} [comm_ring R]

namespace valuation

variables {Γ₀ : Type u} [linear_ordered_comm_group_with_zero Γ₀]
variables (v : valuation R Γ₀)

/-- The elements of `units (valuation_field v)` with norm 1. -/
definition valuation_field_norm_one :=
is_group_hom.ker (units.map (v.on_valuation_field : v.valuation_field →* Γ₀))

/-- `valuation_field_norm_one v is a normal subgroup of `units (valuation_field v)`. -/
instance (v : valuation R Γ₀) : normal_subgroup (valuation_field_norm_one v) :=
by unfold valuation_field_norm_one; apply_instance

namespace value_monoid

def quotient_rel (a b : v.valuation_field) : Prop :=
∃ c : units v.valuation_field, c ∈ v.valuation_field_norm_one ∧ a * c = b

namespace quotient_rel

lemma refl (a : v.valuation_field) : quotient_rel v a a :=
⟨1, is_submonoid.one_mem _, mul_one a⟩

lemma symm (a b : v.valuation_field) : quotient_rel v a b → quotient_rel v b a :=
by { rintro ⟨c, hc, rfl⟩, exact ⟨c⁻¹, is_subgroup.inv_mem hc, c.mul_inv_cancel_right a⟩ }

lemma trans (a b c : v.valuation_field) :
  quotient_rel v a b → quotient_rel v b c → quotient_rel v a c :=
begin
  rintro ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩,
  exact ⟨c * c', is_submonoid.mul_mem hc hc', (mul_assoc _ _ _).symm⟩
end

end quotient_rel

def setoid : setoid (v.valuation_field) :=
{ r := quotient_rel v,
  iseqv := ⟨quotient_rel.refl v, quotient_rel.symm v, quotient_rel.trans v⟩ }

end value_monoid

/-- The value group of the canonical valuation.-/
def value_monoid (v : valuation R Γ₀) : Type u₀ :=
@quotient v.valuation_field (value_monoid.setoid v)

namespace value_monoid
open function

def to_Γ₀ : v.value_monoid → Γ₀ :=
λ x, quotient.lift_on' x v.on_valuation_field $
begin
  rintros a b ⟨c, hc, rfl⟩,
  replace hc : v.on_valuation_field c = 1 := units.ext_iff.mp (is_subgroup.mem_trivial.mp hc),
  rw [v.on_valuation_field.map_mul, hc, mul_one],
end

lemma to_Γ₀_inj : injective (to_Γ₀ v) :=
begin
  rintros ⟨a⟩ ⟨b⟩ h,
  change v.on_valuation_field a = v.on_valuation_field b at h,
  by_cases ha : a = 0,
  { subst a, rw [valuation.map_zero, eq_comm, valuation.zero_iff] at h, rw h },
  { have hb : b ≠ 0,
    { rintro rfl, rw [valuation.map_zero, valuation.zero_iff] at h, exact ha h },
    refine quotient.sound' ⟨(units.mk0 a ha)⁻¹ * (units.mk0 b hb),
      is_subgroup.mem_trivial.mpr _, (units.mk0 a ha).mul_inv_cancel_left _⟩,
    rw ← v.on_valuation_field.ne_zero_iff at hb,
    simp [units.ext_iff, h, hb] }
end

instance : linear_order (v.value_monoid) :=
linear_order.lift (to_Γ₀ v) (to_Γ₀_inj v) infer_instance

lemma to_Γ₀_strict_mono : strict_mono (to_Γ₀ v) := λ a b, id

@[simp] lemma triangle (a : v.valuation_field) :
  to_Γ₀ v (quotient.mk' a) = v.on_valuation_field a := rfl

instance : has_zero (v.value_monoid) := ⟨quotient.mk' 0⟩

instance : has_one  (v.value_monoid) := ⟨quotient.mk' 1⟩

instance : has_inv  (v.value_monoid) :=
⟨λ x, quotient.lift_on' x (λ a, quotient.mk' a⁻¹)
begin
  rintros a b ⟨c, hc, rfl⟩,
  replace hc : v.on_valuation_field c = 1 := units.ext_iff.mp (is_subgroup.mem_trivial.mp hc),
  apply to_Γ₀_inj,
  simp [hc],
end⟩

instance : has_mul  (v.value_monoid) :=
⟨λ x y, quotient.lift_on₂' x y (λ a b, quotient.mk' (a*b))
begin
  rintros a₁ b₁ a₂ b₂ ⟨c₁, hc₁, rfl⟩ ⟨c₂, hc₂, rfl⟩,
  replace hc₁ : v.on_valuation_field c₁ = 1 := units.ext_iff.mp (is_subgroup.mem_trivial.mp hc₁),
  replace hc₂ : v.on_valuation_field c₂ = 1 := units.ext_iff.mp (is_subgroup.mem_trivial.mp hc₂),
  apply to_Γ₀_inj,
  simp [hc₁, hc₂],
end⟩

@[simp] lemma to_Γ₀_zero : to_Γ₀ v 0 = 0 := v.on_valuation_field.map_zero

@[simp] lemma to_Γ₀_one  : to_Γ₀ v 1 = 1 := v.on_valuation_field.map_one

@[simp] lemma to_Γ₀_inv (a) : to_Γ₀ v a⁻¹ = (to_Γ₀ v a)⁻¹ :=
quotient.induction_on' a $ λ x, v.on_valuation_field.map_inv

@[simp] lemma to_Γ₀_mul (a b) : to_Γ₀ v (a*b) = (to_Γ₀ v a) * (to_Γ₀ v b) :=
quotient.induction_on₂' a b $ λ x y, v.on_valuation_field.map_mul x y

instance : group_with_zero (v.value_monoid) :=
begin
  refine_struct {
  .. value_monoid.has_zero v,
  .. value_monoid.has_one v,
  .. value_monoid.has_inv v,
  .. value_monoid.has_mul v, },
  show decidable_eq (value_monoid v),
  { apply_instance },
  show (0 : v.value_monoid) ≠ 1,
  { assume this, replace := congr_arg (to_Γ₀ v) this, simpa using this, },
  all_goals { intros, apply to_Γ₀_inj, simp },
  { exact mul_assoc _ _ _ },
  { apply mul_inv_cancel', intro this, apply_assumption, apply to_Γ₀_inj, simpa }
end

instance : linear_ordered_comm_group_with_zero (v.value_monoid) :=
{ mul_comm := λ a b, to_Γ₀_inj v $ by simpa using mul_comm _ _,
  mul_le_mul_left := λ a b h c,
  begin
    rw ← (to_Γ₀_strict_mono v).le_iff_le at h ⊢,
    simpa using linear_ordered_structure.mul_le_mul_left h _
  end,
  zero_le' := λ a, by { rw ← (to_Γ₀_strict_mono v).le_iff_le, simp },
  .. value_monoid.group_with_zero v,
  .. value_monoid.linear_order v }

/-- The natural quotient map from `units (valuation_field v)` to `value_monoid v`. -/
def mk (v : valuation R Γ₀) :
  valuation_field v →* value_monoid v :=
{ to_fun := quotient.mk',
  map_one' := rfl,
  map_mul' := λ a b, rfl, }

end value_monoid

/-- The canonical valuation on Frac(R/supp(v)), taking values in `value_monoid v`. -/
def valuation_field.canonical_valuation :
valuation (valuation_field v) (value_monoid v) :=
{ map_zero' := rfl,
  map_add' := λ a b,
  begin
    rw ← (value_monoid.to_Γ₀_strict_mono v).le_iff_le,
    rw (value_monoid.to_Γ₀_strict_mono v).monotone.map_max,
    exact v.on_valuation_field.map_add a b
  end,
  .. value_monoid.mk v }
-- ⟨valuation_field.canonical_valuation_v v, valuation_field.canonical_valuation_v.is_valuation v⟩

/-- The canonical valuation on R/supp(v), taking values in `value_monoid v`. -/
definition quotient.canonical_valuation :
  valuation (ideal.quotient (supp v)) (value_monoid v) :=
@comap _ _ _ _ _ _ (localization.of)
  (by apply_instance) (valuation_field.canonical_valuation v)

/-- The canonical valuation on R, taking values in `value_monoid v`. -/
definition canonical_valuation :
  valuation R (value_monoid v) :=
(quotient.canonical_valuation v).comap (ideal.quotient.mk (supp v))

/-- The relation between `v.canonical_valuation r` and `v r`. -/
lemma canonical_valuation_eq (r : R) :
  v.canonical_valuation r = value_monoid.mk v (v.valuation_field_mk r) := rfl

namespace canonical_valuation

-- This looks handy to know but we never actually use it.
/-- Every element of `value_monoid v` is a ratio of things in the image of `canonical_valuation v`.-/
lemma value_monoid.is_ratio (v : valuation R Γ₀) (g : value_monoid v) :
∃ r s : R, s ∉ v.supp ∧ v.canonical_valuation s * g = v.canonical_valuation r :=
begin
  apply quotient.induction_on' g, clear g,
  rintros ⟨⟨r⟩, ⟨s⟩, h⟩,
  change ideal.quotient.mk _ s ∈ _ at h,
  use [r, s],
  split,
  { show s ∉ supp v,
    assume mem_supp,
    erw [localization.fraction_ring.mem_non_zero_divisors_iff_ne_zero,
      (ideal.quotient.eq_zero_iff_mem).2 mem_supp] at h,
    contradiction },
  show value_monoid.mk v _ * value_monoid.mk v _ = value_monoid.mk v _,
  rw ← monoid_hom.map_mul,
  refine congr_arg _ _,
  let rq := ideal.quotient.mk (supp v) r,
  let sq := ideal.quotient.mk (supp v) s,
  show (localization.of sq : valuation_field v) * (localization.mk rq ⟨sq, h⟩) = localization.of rq,
  erw [localization.mk_eq, mul_comm, mul_assoc, units.inv_val _, mul_one],
  refl
end

/-- v can be reconstructed from `canonical_valuation v` by pushing forward along
the map `value_monoid v → Γ₀`. -/
lemma to_Γ₀ :
  (canonical_valuation v).map (monoid_hom.mk (value_monoid.to_Γ₀ v) (value_monoid.to_Γ₀_one v) (value_monoid.to_Γ₀_mul v))
  (value_monoid.to_Γ₀_zero v) (value_monoid.to_Γ₀_strict_mono v).monotone = v :=
ext $ λ r, show v r * (v 1)⁻¹ = v r, by simp

end canonical_valuation -- end of namespace

end valuation -- end of namespace

namespace valuation

variables {Γ₀ : Type u}   [linear_ordered_comm_group_with_zero Γ₀]
variables {Γ'₀ : Type u₁} [linear_ordered_comm_group_with_zero Γ'₀]
variables {Γ''₀ : Type u₂} [linear_ordered_comm_group_with_zero Γ''₀]
variables {Γ₀₃ : Type u₃} [linear_ordered_comm_group_with_zero Γ₀₃]

/-- A valuation is equivalent to its canonical valuation -/
lemma canonical_valuation_is_equiv (v : valuation R Γ₀) :
  v.canonical_valuation.is_equiv v :=
begin
  have h := is_equiv.of_eq (canonical_valuation.to_Γ₀ v),
  symmetry,
  refine h.symm.trans _,
  exact is_equiv_of_map_strict_mono _ _ _,
end

namespace is_equiv

-- Various lemmas about valuations being equivalent.

variables {v : valuation R Γ₀} {v₁ : valuation R Γ'₀} {v₂ : valuation R Γ''₀} {v₃ : valuation R Γ₀₃}

/-- If J ⊆ supp(v) then pulling back the induced valuation on R / J back to R gives a
valuation equivalent to v. -/
lemma on_quot_comap_self {J : ideal R} (hJ : J ≤ supp v) :
  is_equiv ((v.on_quot hJ).comap (ideal.quotient.mk J)) v :=
of_eq (on_quot_comap_eq _ _)

/-- Two valuations on R/J are equivalent iff their pullbacks to R are equivalent. -/
lemma comap_on_quot (J : ideal R) (v₁ : valuation J.quotient Γ'₀) (v₂ : valuation J.quotient Γ''₀) :
  (v₁.comap (ideal.quotient.mk J)).is_equiv (v₂.comap (ideal.quotient.mk J)) ↔ v₁.is_equiv v₂ :=
{ mp  := begin rintros h ⟨x⟩ ⟨y⟩, exact h x y end,
  mpr := λ h, comap _ h }

open localization

/-- If supp(v)=0 then v is equivalent to the pullback of the extension of v to Frac(R). -/
lemma on_frac_comap_self {R : Type u₀} [integral_domain R] (v : valuation R Γ₀) (hv : supp v = 0) :
  is_equiv ((v.on_frac hv).comap of) v :=
of_eq (on_frac_comap_eq v hv)

/-- If R is an ID then two valuations on R are equivalent iff their extensions to Frac(R) are
equivalent. -/
lemma comap_on_frac {R : Type u₀} [integral_domain R]
(v₁ : valuation (fraction_ring R) Γ'₀) (v₂ : valuation (fraction_ring R) Γ''₀) :
  (v₁.comap of).is_equiv (v₂.comap of) ↔ is_equiv v₁ v₂ :=
{ mp  := begin
    rintros h ⟨x⟩ ⟨y⟩,
    erw [← comap_on_frac_eq v₁, ← comap_on_frac_eq v₂],
    show _ * _ ≤ _ * _ ↔ _ * _ ≤ _ * _,
    erw div_le_div', erw div_le_div',
    { repeat {erw ← valuation.map_mul},
      exact h _ _ },
    all_goals { intro H,
      erw [← mem_supp_iff, comap_supp, (supp _).eq_bot_of_prime] at H,
      simp at H,
      replace H := fraction_ring.eq_zero_of _ H,
      refine fraction_ring.mem_non_zero_divisors_iff_ne_zero.mp _ H,
      apply subtype.val_prop _,
      apply_instance },
  end,
  mpr := λ h, h.comap _ }

/-- [Wed 1.27] (iii) -> first part of (ii). -/
lemma supp_eq (h : v₁.is_equiv v₂) : supp v₁ = supp v₂ :=
ideal.ext $ λ r,
calc r ∈ supp v₁ ↔ v₁ r = 0    : iff.rfl
             ... ↔ v₁ r ≤ v₁ 0 : by simp
             ... ↔ v₂ r ≤ v₂ 0 : h r 0
             ... ↔ v₂ r = 0    : by simp
             ... ↔ r ∈ supp v₂ : iff.rfl

/-- If v₁ and v₂ are equivalent then v₁(r)=1 → v₂(r)=1. -/
lemma v_eq_one_of_v_eq_one (h : v₁.is_equiv v₂) {r : R} : v₁ r = 1 → v₂ r = 1 :=
begin
  rw [←v₁.map_one, ←v₂.map_one],
  intro hr,
  exact le_antisymm ((h r 1).1 (le_of_eq hr)) ((h 1 r).1 (le_of_eq hr.symm)),
end

/-- If v₁ and v₂ are equivalent then v₁(r)=1 ↔ v₂(r)=1. -/
lemma v_eq_one (h : v₁.is_equiv v₂) (r : R) : v₁ r = 1 ↔ v₂ r = 1 :=
⟨v_eq_one_of_v_eq_one h,v_eq_one_of_v_eq_one h.symm⟩

/-- If v₁ and v₂ are equivalent then their canonical valuations are too. -/
lemma canonical_equiv_of_is_equiv (h : v₁.is_equiv v₂) :
  (canonical_valuation v₁).is_equiv (canonical_valuation v₂) :=
begin
  refine is_equiv.trans v₁.canonical_valuation_is_equiv _,
  refine is_equiv.trans h _,
  apply is_equiv.symm,
  exact v₂.canonical_valuation_is_equiv
end

end is_equiv -- end of namespace

/-- The supports of v and v.canonical_valuation are equal. -/
lemma canonical_valuation_supp (v : valuation R Γ₀) :
  supp (v.canonical_valuation) = supp v := (canonical_valuation_is_equiv v).supp_eq

section Wedhorn1_27_equivalences

variables {v : valuation R Γ₀} {v₁ : valuation R Γ'₀} {v₂ : valuation R Γ''₀} {v₃ : valuation R Γ₀₃}

open is_group_hom quotient_group function

-- We now start on the equivalences of Wedhorn 1.27. The first one is easy.

/-- Wedhorn 1.27 (i) → (iii) : An ordered isomorphism of value groups which commutes with
canonical valuations implies that valuations are equivalent. -/
lemma of_inj_value_monoid (f : v₁.value_monoid →* v₂.value_monoid) (h₀ : f 0 = 0) (hf : strict_mono f)
(H : v₂.canonical_valuation = v₁.canonical_valuation.map f h₀ (hf.monotone)) :
  v₁.is_equiv v₂ :=
begin
  refine (v₁.canonical_valuation_is_equiv.symm).trans _,
  refine (is_equiv.trans _ (v₂.canonical_valuation_is_equiv)),
  rw H,
  symmetry,
  exact is_equiv_of_map_strict_mono _ _ _
end

-- These lemmas look slightly ridiculous to a mathematician but they are avoiding equality of
-- types and instead defining and reasoning about maps which mathematicians would call
-- "the identiy map".

/-- Natural map R/supp(v₁) → R/supp(v₂) induced by equality supp(v₁)=supp(v₂). -/
def quot_of_quot_of_eq_supp (h : supp v₁ = supp v₂) : valuation_ID v₁ → valuation_ID v₂ :=
ideal.quotient.lift _ (ideal.quotient.mk _)
(λ r hr, ideal.quotient.eq_zero_iff_mem.2 $ h ▸ hr)

lemma quot_of_quot_of_eq_supp.id (r : valuation_ID v) : quot_of_quot_of_eq_supp (rfl) r = r :=
by rcases r;refl

lemma quot_of_quot_of_eq_supp.comp (h12 : supp v₁ = supp v₂) (h23 : supp v₂ = supp v₃)
  (r : valuation_ID v₁) : quot_of_quot_of_eq_supp h23 (quot_of_quot_of_eq_supp h12 r) =
  quot_of_quot_of_eq_supp (h23 ▸ h12 : supp v₁ = supp v₃) r :=
by rcases r;refl

/-- If supp(v₁)=supp(v₂) then R/supp(v₁) is isomorphic to R/supp(v₂). -/
def valuation_ID.equiv (h : supp v₁ = supp v₂) : valuation_ID v₁ ≃ valuation_ID v₂ :=
{ to_fun := quot_of_quot_of_eq_supp h,
  inv_fun := quot_of_quot_of_eq_supp (h.symm),
  left_inv := λ r, by rw quot_of_quot_of_eq_supp.comp h h.symm; exact quot_of_quot_of_eq_supp.id r,
  right_inv := λ r, by rw quot_of_quot_of_eq_supp.comp h.symm h; exact quot_of_quot_of_eq_supp.id r
}

@[simp] lemma quot_of_quot_of_eq_supp_quotient_mk (h : supp v₁ = supp v₂) :
  quot_of_quot_of_eq_supp h ∘ ideal.quotient.mk _ = ideal.quotient.mk _ :=
funext $ λ x, ideal.quotient.lift_mk

lemma quot_of_quot_of_eq_supp_quotient_mk' (h : supp v₁ = supp v₂) (r : R) :
  quot_of_quot_of_eq_supp h (ideal.quotient.mk _ r) = ideal.quotient.mk _ r :=
by rw ←quot_of_quot_of_eq_supp_quotient_mk h

/-- If supp(v₁)=supp(v₂) then the identity map R/supp(v₁) → R/supp(v₂) is a ring homomorphism. -/
instance quot_of_quot_of_eq_supp.is_ring_hom (h : supp v₁ = supp v₂) :
  is_ring_hom (quot_of_quot_of_eq_supp h) :=
by delta quot_of_quot_of_eq_supp; apply_instance

/-- If supp(v₁)=supp(v₂) then R/supp(v₁) and R/supp(v₂) are isomorphic rings. -/
def quot_equiv_quot_of_eq_supp (h : supp v₁ = supp v₂) : valuation_ID v₁ ≃+* valuation_ID v₂ :=
{ .. ring_hom.of (quot_of_quot_of_eq_supp h),
  .. valuation_ID.equiv h }

/-- If supp(v₁)=supp(v₂) then the triangle R → R/supp(v₁) → R/supp(v₂) commutes. -/
lemma quot_equiv_quot_mk_eq_mk (h : supp v₁ = supp v₂) (r : R) :
  (quot_equiv_quot_of_eq_supp h).to_equiv (ideal.quotient.mk _ r) = ideal.quotient.mk _ r :=
quot_of_quot_of_eq_supp_quotient_mk' h r

lemma quot_of_quot_of_eq_supp_inj (h : supp v₁ = supp v₂) : injective (quot_of_quot_of_eq_supp h) :=
injective_of_left_inverse (quot_equiv_quot_of_eq_supp h).left_inv

lemma valuation_ID_le_of_le_of_equiv (h : v₁.is_equiv v₂) (a b : valuation_ID v₁) :
  (a ≤ b) ↔
  quot_of_quot_of_eq_supp (is_equiv.supp_eq h) a ≤ quot_of_quot_of_eq_supp (is_equiv.supp_eq h) b :=
by rcases a; rcases b; exact (h a b)

/-- If v₁ and v₂ are equivalent, then the associated preorders on
R/supp(v₁)=R/supp(v₂) are equivalent. -/
def valuation_ID.preorder_equiv (h : v₁.is_equiv v₂) :
  preorder_equiv (valuation_ID v₁) (valuation_ID v₂) :=
{ le_map := valuation_ID_le_of_le_of_equiv h,
  ..valuation_ID.equiv h.supp_eq
}

section valuation_field

open localization

/-- The natural map Frac(R/supp(v₁)) → Frac(R/supp(v₂)) if supp(v₁) = supp(v₂). -/
def valfield_of_valfield_of_eq_supp (h : supp v₁ = supp v₂) :
  valuation_field v₁ → valuation_field v₂ :=
fraction_ring.map (quot_of_quot_of_eq_supp h) (quot_of_quot_of_eq_supp_inj h)

/-- The triangle R → Frac(R/supp(v₁)) → Frac(R/supp(v₂)) commutes if supp(v₁)=supp(v₂). -/
lemma valfield_of_valfield_of_eq_supp_quotient_mk (h : supp v₁ = supp v₂) (r : R) :
  valfield_of_valfield_of_eq_supp h (of $ ideal.quotient.mk _ r) = of (ideal.quotient.mk _ r) :=
begin
  unfold valfield_of_valfield_of_eq_supp,
  rw fraction_ring.map_of,
  rw quot_of_quot_of_eq_supp_quotient_mk',
end

/-- If supp(v₁)=supp(v₂) then the natural map Frac(R/supp(v₁)) → Frac(R/supp(v₂)) is a
homomorphism of fields. -/
instance (h : supp v₁ = supp v₂) : is_field_hom (valfield_of_valfield_of_eq_supp h) :=
by delta valfield_of_valfield_of_eq_supp; apply_instance

-- This should be possible using type class inference but there are max class
-- instance issues.
/-- If supp(v₁)=supp(v₂) then the natural map Frac(R/supp(v₁)) → Frac(R/supp(v₂)) is a
homomorphism of monoids. -/
instance (h : supp v₁ = supp v₂) : is_monoid_hom (valfield_of_valfield_of_eq_supp h) :=
is_semiring_hom.is_monoid_hom (valfield_of_valfield_of_eq_supp h)

/-- If supp(v₁)=supp(v₂) then the natural map Frac(R/supp(v₁)) → Frac(R/supp(v₂)) is an
isomorphism of rings. -/
def valfield_equiv_valfield_of_eq_supp (h : supp v₁ = supp v₂) :
  valuation_field v₁ ≃+* valuation_field v₂ :=
fraction_ring.equiv_of_equiv (quot_equiv_quot_of_eq_supp h)

lemma valfield_equiv_eq_valfield_of_valfield (h : supp v₁ = supp v₂) (q : valuation_field v₁) :
(valfield_equiv_valfield_of_eq_supp h).to_equiv q = valfield_of_valfield_of_eq_supp h q := rfl

lemma valfield_equiv_valfield_mk_eq_mk (h : supp v₁ = supp v₂) (r : R) :
  (valfield_equiv_valfield_of_eq_supp h).to_equiv (of $ ideal.quotient.mk _ r)
  = of (ideal.quotient.mk _ r) :=
valfield_of_valfield_of_eq_supp_quotient_mk h r

/-- If v₁ and v₂ are equivalent then the induced valuations on R/supp(v₁) and R/supp(v₂)
(pulled back to R/supp(v₁) are equivalent. -/
lemma is_equiv.comap_quot_of_quot (h : v₁.is_equiv v₂) :
  (v₁.on_quot (set.subset.refl _)).is_equiv
  ((v₂.on_quot (set.subset.refl _)).comap (quot_of_quot_of_eq_supp h.supp_eq)) :=
begin
  rw [← is_equiv.comap_on_quot, ← comap_comp],
  simp [h],
end

/-- If v₁ and v₂ are equivalent then the induced valuations on Frac(R/supp(v₁)) and
Frac(R/supp(v₂)) [pulled back] are equivalent. -/
lemma is_equiv.on_valuation_field_is_equiv (h : v₁.is_equiv v₂) :
  v₁.on_valuation_field.is_equiv
  (v₂.on_valuation_field.comap (valfield_of_valfield_of_eq_supp h.supp_eq)) :=
begin
  delta valfield_of_valfield_of_eq_supp, delta on_valuation_field,
  erw [← is_equiv.comap_on_frac, ← comap_comp, on_frac_comap_eq],
  simp [comap_comp, h.comap_quot_of_quot],
end

/-- The valuation rings of two equivalent valuations are isomorphic (as types). -/
def val_ring_equiv_of_is_equiv_aux (h : v₁.is_equiv v₂) :
v₁.valuation_ring ≃ v₂.valuation_ring :=
equiv.subtype_congr (valfield_equiv_valfield_of_eq_supp h.supp_eq).to_equiv $
begin
  intro x,
  show _ ≤ _ ↔ _ ≤ _,
  erw [← v₁.on_valuation_field.map_one, h.on_valuation_field_is_equiv],
  convert iff.refl _,
  symmetry,
  exact valuation.map_one _,
end

/-- The valuation rings of two equivalent valuations are isomorphic as rings. -/
def val_ring_equiv_of_is_equiv (h : v₁.is_equiv v₂) : v₁.valuation_ring ≃+* v₂.valuation_ring :=
{ map_add' := λ x y, subtype.val_injective $
    (valfield_equiv_valfield_of_eq_supp h.supp_eq).map_add x y,
  map_mul' := λ x y, subtype.val_injective $
    (valfield_equiv_valfield_of_eq_supp h.supp_eq).map_mul x y,
  .. val_ring_equiv_of_is_equiv_aux h, }

-- we omit the proof that the diagram {r | v₁ r ≤ 1} → v₁.valuation_ring → v₂.valuation_ring
-- commutes.

lemma valfield_le_of_le_of_equiv (h : v₁.is_equiv v₂) (a b : valuation_field v₁) :
  (a ≤ b) ↔ valfield_of_valfield_of_eq_supp (h.supp_eq) a ≤
    valfield_of_valfield_of_eq_supp (h.supp_eq) b :=
calc a ≤ b ↔ v₁.on_valuation_field a ≤ v₁.on_valuation_field b : iff.rfl
       ... ↔ _ : h.on_valuation_field_is_equiv a b

def valfield.preorder_equiv (h : v₁.is_equiv v₂) :
  preorder_equiv (valuation_field v₁) (valuation_field v₂) :=
{ le_map := valfield_le_of_le_of_equiv h,
  ..(valfield_equiv_valfield_of_eq_supp h.supp_eq).to_equiv
}

-- units

def valfield_units_of_valfield_units_of_eq_supp (h : supp v₁ = supp v₂) :
  units (valuation_field v₁) → units (valuation_field v₂) :=
units.map' $ valfield_of_valfield_of_eq_supp h

instance valfield_units.is_group_hom (h : supp v₁ = supp v₂) :
is_group_hom (valfield_units_of_valfield_units_of_eq_supp h) :=
by unfold valfield_units_of_valfield_units_of_eq_supp; apply_instance

lemma units_valfield_of_units_valfield_of_eq_supp_mk
  (h : supp v₁ = supp v₂) (r : R) (hr : r ∉ supp v₁) :
  valfield_units_of_valfield_units_of_eq_supp h (units_valfield_mk v₁ r hr)
  = units_valfield_mk v₂ r (h ▸ hr) := units.ext $ valfield_equiv_valfield_mk_eq_mk h r

def valfield_units_equiv_units_of_eq_supp (h : supp v₁ = supp v₂) :
(units (valuation_field v₁)) ≃* (units (valuation_field v₂)) :=
units.map_equiv { .. valfield_equiv_valfield_of_eq_supp h }

end valuation_field -- section

lemma valfield_units_equiv_units_mk_eq_mk (h : supp v₁ = supp v₂) (r : R) (hr : r ∉ supp v₁):
(valfield_units_equiv_units_of_eq_supp h).to_equiv (units_valfield_mk v₁ r hr) =
units_valfield_mk v₂ r (h ▸ hr) := units_valfield_of_units_valfield_of_eq_supp_mk h r hr

def valfield_units_preorder_equiv (h : v₁.is_equiv v₂) :
  preorder_equiv (units (valuation_field v₁)) (units (valuation_field v₂)) :=
{ le_map := λ u v, @le_equiv.le_map _ _ _ _ (valfield.preorder_equiv h) u.val v.val,
  ..valfield_units_equiv_units_of_eq_supp (h.supp_eq)
 }

-- This explicit instance helps type class inference; it's a shortcut.
-- The "by apply_instance" proof needs
-- set_option class.instance_max_depth 35
instance (h : is_equiv v₁ v₂) :
is_subgroup ((valfield_units_of_valfield_units_of_eq_supp (is_equiv.supp_eq h)) ⁻¹'
  (valuation_field_norm_one v₂)) :=
normal_subgroup.to_is_subgroup _

-- Same here -- the `by apply_instance` proof needs max_depth 35
instance (h : is_equiv v₁ v₂) : group (quotient_group.quotient
  ((valfield_units_of_valfield_units_of_eq_supp (is_equiv.supp_eq h)) ⁻¹'
    (valuation_field_norm_one v₂))) :=
quotient_group.group
  ((valfield_units_of_valfield_units_of_eq_supp (is_equiv.supp_eq h)) ⁻¹'
    (valuation_field_norm_one v₂))

lemma val_one_iff_unit_val_one (x : units (valuation_field v)) :
  x ∈ valuation_field_norm_one v ↔ v.on_valuation_field x = 1 :=
calc x ∈ valuation_field_norm_one v ↔
  (units.map (v.on_valuation_field : v.valuation_field →* Γ₀) x = 1) : is_subgroup.mem_trivial
  ... ↔ v.on_valuation_field x = 1 : units.ext_iff

lemma is_equiv.norm_one_eq_norm_one (h : is_equiv v₁ v₂) :
  valfield_units_of_valfield_units_of_eq_supp (is_equiv.supp_eq h) ⁻¹' valuation_field_norm_one v₂
  = valuation_field_norm_one v₁ :=
begin
  ext x,
  rw [set.mem_preimage, val_one_iff_unit_val_one x,
    is_equiv.v_eq_one (is_equiv.on_valuation_field_is_equiv h) x, val_one_iff_unit_val_one],
  refl,
end

-- group part of Wedhorn 1.27 (iii) -> (i)
def is_equiv.value_mul_equiv (h : is_equiv v₁ v₂) :
  (value_monoid v₁) ≃* (value_monoid v₂) :=
{ to_fun := λ x, quotient.lift_on' x ((valuation_field.canonical_valuation v₂).comap (valfield_of_valfield_of_eq_supp h.supp_eq))
    begin
      rintros a b ⟨c, hc, rfl⟩,
      rw valuation.map_mul,
      convert (mul_one _).symm,
      rw val_one_iff_unit_val_one at hc,
      rw h.on_valuation_field_is_equiv.v_eq_one c at hc,
      suffices : v₂.on_valuation_field.is_equiv (valuation_field.canonical_valuation v₂),
      { have tmp := (this.comap (valfield_of_valfield_of_eq_supp _)),
        rwa tmp.v_eq_one at hc, },
      intros a b, exact iff.rfl
    end,
  inv_fun :=  λ x, quotient.lift_on' x ((valuation_field.canonical_valuation v₁).comap (valfield_of_valfield_of_eq_supp h.symm.supp_eq))
    begin
      rintros a b ⟨c, hc, rfl⟩,
      rw valuation.map_mul,
      convert (mul_one _).symm,
      rw val_one_iff_unit_val_one at hc,
      rw h.symm.on_valuation_field_is_equiv.v_eq_one c at hc,
      suffices : v₁.on_valuation_field.is_equiv (valuation_field.canonical_valuation v₁),
      { have tmp := (this.comap (valfield_of_valfield_of_eq_supp _)),
        rwa tmp.v_eq_one at hc, },
      intros a b, exact iff.rfl
    end,
  left_inv := by { rintro ⟨a⟩, apply quotient.sound',
    refine ⟨1, is_submonoid.one_mem _, _⟩,
    rw [units.coe_one, mul_one],
    exact (valfield_equiv_valfield_of_eq_supp h.supp_eq).to_equiv.left_inv a },
  right_inv := by { rintro ⟨a⟩, apply quotient.sound',
    refine ⟨1, is_submonoid.one_mem _, _⟩,
    rw [units.coe_one, mul_one],
    exact (valfield_equiv_valfield_of_eq_supp h.symm.supp_eq).to_equiv.left_inv a },
  map_mul' :=
  begin
    rintro ⟨a⟩ ⟨b⟩, apply quotient.sound',
    refine ⟨1, is_submonoid.one_mem _, _⟩,
    rw [units.coe_one, mul_one],
    exact is_ring_hom.map_mul _,
  end }

-- ordering part of 1.27 (iii) -> (i)
def is_equiv.value_monoid_order_equiv_aux (h : is_equiv v₁ v₂) (x y : value_monoid v₁) (h2 : x ≤ y) :
  h.value_mul_equiv x ≤ h.value_mul_equiv y :=
begin
  induction x with x, induction y, swap, refl, swap, refl,
  exact (is_equiv.on_valuation_field_is_equiv h x y).1 h2,
end

def is_equiv.value_monoid_le_equiv (h : is_equiv v₁ v₂) :
  (value_monoid v₁) ≃≤ (value_monoid v₂) :=
{ le_map := λ x y, linear_order_le_iff_of_monotone_injective
  (h.value_mul_equiv.to_equiv.bijective.1)
  (is_equiv.value_monoid_order_equiv_aux h) x y
   ..h.value_mul_equiv}

def is_equiv.value_mul_equiv_monotone (h : is_equiv v₁ v₂) :
  monotone (h.value_mul_equiv) := λ x y,
  (@@le_equiv.le_map _ _ (is_equiv.value_monoid_le_equiv h)).1

def is_equiv.value_mul_equiv_map_zero (h : is_equiv v₁ v₂) :
  h.value_mul_equiv 0 = 0 :=
begin
  apply quotient.sound',
  refine ⟨1, is_submonoid.one_mem _, _⟩,
  rw [units.coe_one, mul_one],
  exact is_ring_hom.map_zero _,
end

lemma is_equiv.with_zero_value_mul_equiv_mk_eq_mk (h : v₁.is_equiv v₂) :
  (canonical_valuation v₁).map
    h.value_mul_equiv.to_monoid_hom h.value_mul_equiv_map_zero h.value_mul_equiv_monotone =
  canonical_valuation v₂ :=
begin
  ext r, apply quotient.sound',
  refine ⟨1, is_submonoid.one_mem _, _⟩,
  rw [units.coe_one, mul_one],
  apply valfield_of_valfield_of_eq_supp_quotient_mk,
end

end Wedhorn1_27_equivalences -- section

end valuation


#sanity_check
#doc_blame


