import valuation.basic

import for_mathlib.quotient_group
import for_mathlib.subgroup
import for_mathlib.group -- group_equiv
import for_mathlib.order -- preorder.lift'
/-

The purpose of this file is to define a "canonical" valuation equivalent to
a given valuation. The whole raison d'etre for this is that there are set-theoretic
issues with the equivalence "relation" on valuations, because the target group
Gamma can be arbitrary.

The main idea is this. If v : R → Γ ∪ {0} is an arbitrary valuation,
then v extends to a valuation on K = Frac(R/supp(v)) and hence to a group
homomorphism K^* → Γ, whose kernel is A^*, the units in the valuation ring
(or equivalently the things in K^* of norm at most 1). This embeds K^*/A^*
into Γ and hence gives K^*/A^* the structure of a linearly ordered commutative group.
There is an induced map R → (K^*/A^*) ∪ {0}, and we call this the
_canonical valuation_ associated to v, and this valuation is equivalent to v.
A technical advantage that this valuation has from the point of view
of Lean's type theory is that if R is in universe u₁ and Γ in universe u₂,
then v : valuation R Γ will be in universe `max u₁ u₂` but the canonical
valuation will just be in universe u₁. In particular, if v and v' are equivalent
then their associated canonical valuations are isomorphic and furthermore in the
same universe.

All of the below names are in the `valuation` namespace.

`value_group v` is the totally ordered group $K^*/A^* (note that it is
isomorphic to the subgroup of Γ which Wedhorn calls the value group), and
`value_group.to_Γ` is the group homomorphism to \Gamma.
`canonical_valuation v` is the canonical valuation.
`canonical_valuation.to_\Gamma v` is the lemma that says that we can
recover v from the canonical valuation using the group homomorphism
from K^*/A^* to Gamma.

We then prove some of Proposition-and-Definition 1.27 of Wedhorn,
where we note that we used (iii) for the definition, and
we're now using a different definition to Wedhorn for the value group
(because it's isomorphic so no mathematician will care, and
it's easier for us because it's in a smaller universe).

TODO: Do we ever actually use 1.27 now? KMB has left part of it sorried.

TODO: Do we need any of the dead code commented out at the end of
the file? KMB suspects not.
This dead code is all about the workaround we had for getting down
to R's universe from Gamma's universe before Johan's idea of using
the canonical valuation.

-/

local attribute [instance] classical.prop_decidable
noncomputable theory

universes u u₀ u₁ u₂ u₃

variables {R : Type u₀} [comm_ring R]

namespace valuation
open with_zero

variables {Γ : Type u} [linear_ordered_comm_group Γ]
variables (v : valuation R Γ)

section canonical_equivalent_valuation

instance : comm_group (units (valuation_field v)) := by apply_instance

instance valuation.units_preorder : preorder (units (valuation_field v)) :=
{ le := λ u v, u.val ≤ v.val,
  le_refl := le_refl,
  le_trans := λ _ _ _, le_trans
}

definition valuation_field_norm_one := is_group_hom.ker v.on_valuation_field.unit_map

instance (v : valuation R Γ) : normal_subgroup (valuation_field_norm_one v) :=
by unfold valuation_field_norm_one; apply_instance

/-- The value group of the canonical valuation.-/
def value_group (v : valuation R Γ) : Type u₀ :=
quotient_group.quotient (valuation_field_norm_one v)

def value_group_quotient (v : valuation R Γ) :
units (valuation_field v) → value_group v :=
quotient.mk'

instance value_group.comm_group : comm_group (value_group v) :=
by unfold value_group; apply_instance

def value_group.to_Γ (v : valuation R Γ) :
value_group v → Γ :=
quotient_group.lift (valuation_field_norm_one v) v.on_valuation_field.unit_map $
  λ x, (is_group_hom.mem_ker _).1

instance : is_group_hom (value_group.to_Γ v) :=
by unfold value_group.to_Γ; apply_instance

instance value_group_quotient.is_group_hom :
is_group_hom (value_group_quotient v) := ⟨λ _ _, rfl⟩

-- KMB now worried that this should change to λ s t, s ≤ t with possible breakage
instance : linear_order (value_group v) :=
{ le := λ a' b',
    quotient.lift_on₂' a' b' (λ s t, v.on_valuation_field ↑s ≤ v.on_valuation_field ↑t) $
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

lemma mk_le_mk_iff (x y : units (valuation_field v)) :
  v.value_group_quotient x ≤ v.value_group_quotient y ↔
  v.on_valuation_field x ≤ v.on_valuation_field y := iff.rfl

instance : linear_ordered_comm_group (value_group v) :=
{ mul_le_mul_left := begin rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩,
    change v.on_valuation_field a ≤ v.on_valuation_field b at h,
    change value_group_quotient v c * value_group_quotient v a
    ≤ value_group_quotient v c * value_group_quotient v b,
    rw ←is_group_hom.mul (value_group_quotient v),
    rw ←is_group_hom.mul (value_group_quotient v),
    change v.on_valuation_field (c * a) ≤ v.on_valuation_field (c * b),
    rw v.on_valuation_field.map_mul,
    rw v.on_valuation_field.map_mul,
    exact with_zero.mul_le_mul_left _ _ h _
end}

lemma value_group.to_Γ_monotone :
  monotone (value_group.to_Γ v) :=
begin
  rintros ⟨x⟩ ⟨y⟩,
  erw [mk_le_mk_iff, ← unit_map_eq, ← unit_map_eq, with_bot.some_le_some],
  exact id,
end

lemma value_group.to_Γ_injective :
  function.injective (value_group.to_Γ v) :=
quotient_group.injective_ker_lift _

lemma value_group.to_Γ_strict_mono :
  strict_mono (value_group.to_Γ v) :=
strict_mono_of_monotone_of_injective
  (value_group.to_Γ_monotone _)
  (value_group.to_Γ_injective _)

-- The canonical valuation associated to v is the obvious map
-- from R to value_group v := Frac(R/supp(v)) / A^*
-- (thought of as K^*/A^* union 0)

-- First define a valuation on K
definition valuation_field.canonical_valuation_v :
valuation_field v → with_zero (value_group v) :=
λ k, dite (k = 0) (λ _, 0)
  (λ h, value_group_quotient v ⟨k,k⁻¹,mul_inv_cancel h, inv_mul_cancel h⟩)

instance valuation_field.canonical_valuation_v.is_valuation :
is_valuation (valuation_field.canonical_valuation_v v) :=
{ map_zero := dif_pos rfl,
  map_one := begin unfold valuation_field.canonical_valuation_v, rw dif_neg zero_ne_one.symm,
    apply option.some_inj.2,
    convert is_group_hom.one (value_group_quotient v),
    exact inv_one
  end,
  map_mul := λ x y, begin
    unfold valuation_field.canonical_valuation_v,
    split_ifs with hxy hx hy hy hx hy hy,
    { simp },
    { simp },
    { simp },
    { exfalso, exact or.elim (mul_eq_zero.1 hxy) hx hy},
    { exfalso, exact hxy (hx.symm ▸ zero_mul y)},
    { exfalso, exact hxy (hx.symm ▸ zero_mul y)},
    { exfalso, exact hxy (hy.symm ▸ mul_zero x)},
    apply option.some_inj.2,
    show value_group_quotient v
      {val := x * y, inv := (x * y)⁻¹, val_inv := _, inv_val := _} =
      value_group_quotient v
      {val := x * y, inv := _, val_inv := _, inv_val := _},
    apply congr_arg,
    apply units.ext,
    refl,
  end,
  map_add := λ x y, begin
    unfold valuation_field.canonical_valuation_v,
    split_ifs with hxy hx hy hy hx hy hy,
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

/-- The canonical valuation on Frac(R/supp(v)) -/
def valuation_field.canonical_valuation :
valuation (valuation_field v) (value_group v) :=
⟨valuation_field.canonical_valuation_v v, valuation_field.canonical_valuation_v.is_valuation v⟩

lemma valuation_field.canonical_valuation_unit :
unit_map (valuation_field.canonical_valuation v) = value_group_quotient v :=
begin
  -- really hard to get to the dite
  ext x,
  rw ←option.some_inj,
  rw unit_map_eq,
  show dite (x.val = 0) (λ (_x : x.val = 0), (0 : with_zero (value_group v)))
      (λ (h : ¬x.val = 0),
        (value_group_quotient v {val := ↑x, inv := (↑x)⁻¹, val_inv := _, inv_val := _})) =
    some (value_group_quotient v x),
  -- at last!
  split_ifs with h,
  { change x.val = 0 at h,
    have h2 := x.val_inv,
    rw [h, zero_mul] at h2,
    exfalso, revert h2,
    simp
  },
  { show some _ = some _,
    congr,
    apply units.ext,
    refl
  }
end

/-- The canonical valuation on R/supp(v) -/
definition quotient.canonical_valuation (v : valuation R Γ) :
  valuation (ideal.quotient (supp v)) (value_group v) :=
@comap _ _ _ _ (valuation_field.canonical_valuation v) _ _ (localization.of)
  (by apply_instance)

/-- The canonical valuation on R -/
definition canonical_valuation (v : valuation R Γ) :
  valuation R (value_group v) :=
comap (quotient.canonical_valuation v) (ideal.quotient.mk (supp v))

end canonical_equivalent_valuation

namespace canonical_valuation

-- everything in the image of the value group is a ratio of things
-- coming from the ring
-- Remark (KMB) -- writing this code was surprisingly painful
-- Remark (KMB) -- I am not even sure we ever use it!
lemma value_group.is_ratio (v : valuation R Γ) (g : value_group v) :
∃ r s : R, r ∉ supp v ∧ s ∉ supp v ∧ canonical_valuation v s * g = canonical_valuation v r :=
begin
  rcases g with ⟨u, u', huu', hu'u⟩,
  rcases u with ⟨⟨r⟩, ⟨s⟩, h⟩,
  change ideal.quotient.mk _ s ∈ _ at h,
  use r, use s,
  have hs : s ∉ supp v,
  { intro h2,
    rw @localization.fraction_ring.mem_non_zero_divisors_iff_ne_zero
      (valuation_ID v) at h,
    rw (ideal.quotient.eq_zero_iff_mem).2 h2 at h,
    apply h, refl,
  },
  have hr : r ∉ supp v,
  {
    change (localization.mk (submodule.quotient.mk r) (⟨submodule.quotient.mk s, h⟩) *
      u' : valuation_field v) = 1 at huu',
    intro hr,
    rw (submodule.quotient.mk_eq_zero _).2 hr at huu',
    have : (localization.of (ideal.quotient.mk (supp v) 0) : valuation_field v) / (localization.of (ideal.quotient.mk (supp v) s) : valuation_field v) * u' = 1,
      simpa using huu',
    rw ideal.quotient.mk_zero at this,
    change ((0 : valuation_field v) / localization.of (ideal.quotient.mk (supp v) s) * u' = 1) at this,
    rw _root_.zero_div at this,
    rw zero_mul at this,
    revert this, simp,
  },
  split, exact hr, split, exact hs,
  let rq := ideal.quotient.mk (supp v) r,
  let sq := ideal.quotient.mk (supp v) s,
  have hr' : rq ≠ 0,
    intro h2, apply hr, exact ideal.quotient.eq_zero_iff_mem.1 h2,
  have hs' : sq ≠ 0,
    intro h2, apply hs, exact ideal.quotient.eq_zero_iff_mem.1 h2,
show (valuation_field.canonical_valuation_v v (localization.of sq)) *
  ↑(value_group_quotient v _)
 = (valuation_field.canonical_valuation_v v (localization.of rq)),
  unfold valuation_field.canonical_valuation_v,
  split_ifs,
    exfalso, exact hs' (localization.fraction_ring.eq_zero_of _ h_1),
    exfalso, exact hs' (localization.fraction_ring.eq_zero_of _ h_1),
    exfalso, exact hr' (localization.fraction_ring.eq_zero_of _ h_2),
  show some _ = some _,
  congr,
  show value_group_quotient v _ * value_group_quotient v _ = value_group_quotient v _,
  rw ←(value_group_quotient.is_group_hom v).mul,
  congr,
  apply units.ext,
  show localization.of sq * _ = localization.of rq,
  suffices : (localization.of sq : valuation_field v) * (localization.mk rq ⟨sq, h⟩ : valuation_field v) = localization.of rq,
    convert this,
  rw localization.mk_eq,
  rw mul_comm,
  rw mul_assoc,
  convert mul_one _,
  convert units.inv_val _,
end

-- This lemma shows that the valuation v can be reconstructed from its
-- associated canonical valuation
lemma to_Γ :
(canonical_valuation v).map (value_group.to_Γ v)
  (value_group.to_Γ_monotone _) = v :=
begin
  rw valuation.ext,
  intro r,
  change with_zero.map _ _ = _,
  destruct (v r),
  { intro h,
    rw h,
    change r ∈ supp v at h,
    suffices : canonical_valuation v r = 0,
      rw this, refl,
    show valuation_field.canonical_valuation_v v _ = 0,
    rw ideal.quotient.eq_zero_iff_mem.2 h,
    exact (valuation_field.canonical_valuation v).map_zero,
  },
  { intro g,
    intro hr,
    rw hr,
    have h2 : v r ≠ none,
      rw hr, simp,
    change r ∉ supp v at h2,
    let r' := (ideal.quotient.mk (supp v) r),
    have hr' : r' ≠ 0,
      intro hr', apply h2, exact (submodule.quotient.mk_eq_zero _).1 hr',
    let r'' := localization.of r',
    have hr'' : r'' ≠ 0,
      intro hr'', apply hr', exact localization.fraction_ring.eq_zero_of r' hr'',
    show with_zero.map (value_group.to_Γ v)
      (valuation_field.canonical_valuation_v v
         (r'')) = some g,
    unfold valuation_field.canonical_valuation_v,
    split_ifs with h1,
      contradiction,
    show some (v.on_valuation_field.unit_map ⟨r'',r''⁻¹,_,_⟩) = some g,
    rw unit_map_eq,
    rw ←hr,
    show (on_valuation_field v) (r'') = v r,
    let v' := on_quot v (le_refl _),
    have hv' : supp v' = 0,
      rw supp_quot_supp,
      simp,
    show v'.on_frac_val hv' ⟦⟨r',1⟩⟧ = v r,
    rw on_frac_val_mk,
    show v' r' / v' 1 = v r,
    rw v'.map_one,
    suffices : v' r' = v r,
      simpa using this,
    refl,
  }
end

end canonical_valuation

end valuation

namespace valuation
variables {Γ : Type u}   [linear_ordered_comm_group Γ]
variables {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]
variables {Γ₃ : Type u₃} [linear_ordered_comm_group Γ₃]

/-- A valuation is equivalent to its canonical valuation -/
lemma canonical_valuation_is_equiv (v : valuation R Γ) :
  v.canonical_valuation.is_equiv v :=
begin
  symmetry,
  convert is_equiv_of_map_of_strict_mono
    (value_group.to_Γ v)
    (value_group.to_Γ_strict_mono _),
  symmetry,
  exact canonical_valuation.to_Γ v,
end

namespace is_equiv

-- Various lemmas about valuations being equivalent.

variables {v : valuation R Γ} {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} {v₃ : valuation R Γ₃}

lemma on_quot_comap_self {J : ideal R} (hJ : J ≤ supp v) :
  is_equiv ((v.on_quot hJ).comap (ideal.quotient.mk J)) v :=
of_eq (on_quot_comap_eq _ _)

lemma comap_on_quot (J : ideal R) (v₁ : valuation J.quotient Γ₁) (v₂ : valuation J.quotient Γ₂) :
  (v₁.comap (ideal.quotient.mk J)).is_equiv (v₂.comap (ideal.quotient.mk J)) ↔ v₁.is_equiv v₂ :=
{ mp  := begin rintros h ⟨x⟩ ⟨y⟩, exact h x y end,
  mpr := λ h, comap _ h }

open localization

lemma on_frac_comap_self {R : Type u₀} [integral_domain R] (v : valuation R Γ) (hv : supp v = 0) :
  is_equiv ((v.on_frac hv).comap of) v :=
of_eq (on_frac_comap_eq v hv)

lemma comap_on_frac {R : Type u₀} [integral_domain R]
(v₁ : valuation (fraction_ring R) Γ₁) (v₂ : valuation (fraction_ring R) Γ₂) :
  (v₁.comap of).is_equiv (v₂.comap of) ↔ is_equiv v₁ v₂ :=
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
      replace H := fraction_ring.eq_zero_of _ H,
      refine fraction_ring.mem_non_zero_divisors_iff_ne_zero.mp _ H,
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

lemma v_eq_one_of_v_eq_one (h : v₁.is_equiv v₂) {r : R} : v₁ r = 1 → v₂ r = 1 :=
begin
  rw [←v₁.map_one, ←v₂.map_one],
  intro hr,
  exact le_antisymm ((h r 1).1 (le_of_eq hr)) ((h 1 r).1 (le_of_eq hr.symm)),
end

lemma v_eq_one (h : v₁.is_equiv v₂) (r : R) : v₁ r = 1 ↔ v₂ r = 1 :=
⟨v_eq_one_of_v_eq_one h,v_eq_one_of_v_eq_one h.symm⟩

end is_equiv

section

variables {v : valuation R Γ} {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} {v₃ : valuation R Γ₃}

open is_group_hom quotient_group function

-- We now start on the equivalences of Wedhorn 1.27. This one is easy.

-- Wedhorn 1.27 (i) => (iii)
lemma of_inj_value_group (f : v₁.value_group → v₂.value_group)
[is_group_hom f] (hf : strict_mono f)
(H : v₂.canonical_valuation = v₁.canonical_valuation.map f (hf.monotone)) :
  v₁.is_equiv v₂ :=
begin
  refine (v₁.canonical_valuation_is_equiv.symm).trans _,
  refine (is_equiv.trans _ (v₂.canonical_valuation_is_equiv)),
  rw H,
  symmetry,
  exact is_equiv_of_map_of_strict_mono _ _
end

def quot_of_quot_of_eq_supp (h : supp v₁ = supp v₂) : valuation_ID v₁ → valuation_ID v₂ :=
ideal.quotient.lift _ (ideal.quotient.mk _)
(λ r hr, ideal.quotient.eq_zero_iff_mem.2 $ h ▸ hr)

lemma quot_of_quot_of_eq_supp.id (r : valuation_ID v) : quot_of_quot_of_eq_supp (rfl) r = r :=
by rcases r;refl

lemma quot_of_quot_of_eq_supp.comp (h12 : supp v₁ = supp v₂) (h23 : supp v₂ = supp v₃)
  (r : valuation_ID v₁) : quot_of_quot_of_eq_supp h23 (quot_of_quot_of_eq_supp h12 r) =
  quot_of_quot_of_eq_supp (h23 ▸ h12 : supp v₁ = supp v₃) r :=
by rcases r;refl

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

instance quot_of_quot_of_eq_supp.is_ring_hom (h : supp v₁ = supp v₂) :
  is_ring_hom (quot_of_quot_of_eq_supp h) :=
by delta quot_of_quot_of_eq_supp; apply_instance

def quot_equiv_quot_of_eq_supp (h : supp v₁ = supp v₂) : valuation_ID v₁ ≃r valuation_ID v₂ :=
{ hom :=quot_of_quot_of_eq_supp.is_ring_hom h,
  ..valuation_ID.equiv h}

def quot_equiv_quot_mk_eq_mk (h : supp v₁ = supp v₂) (r : R) :
  (quot_equiv_quot_of_eq_supp h).to_equiv (ideal.quotient.mk _ r) = ideal.quotient.mk _ r :=
quot_of_quot_of_eq_supp_quotient_mk' h r

lemma quot_of_quot_of_eq_supp_inj (h : supp v₁ = supp v₂) : injective (quot_of_quot_of_eq_supp h) :=
injective_of_left_inverse (quot_equiv_quot_of_eq_supp h).left_inv

lemma valuation_ID_le_of_le_of_equiv (h : v₁.is_equiv v₂) (a b : valuation_ID v₁) :
  (a ≤ b) ↔
  quot_of_quot_of_eq_supp (is_equiv.supp_eq h) a ≤ quot_of_quot_of_eq_supp (is_equiv.supp_eq h) b :=
by rcases a; rcases b; exact (h a b)

def valuation_ID.preorder_equiv (h : v₁.is_equiv v₂) :
  preorder_equiv (valuation_ID v₁) (valuation_ID v₂) :=
{ preorder_iso := valuation_ID_le_of_le_of_equiv h,
  ..valuation_ID.equiv h.supp_eq
}

section
open localization

def valfield_of_valfield_of_eq_supp (h : supp v₁ = supp v₂) :
  valuation_field v₁ → valuation_field v₂ :=
fraction_ring.map (quot_of_quot_of_eq_supp h) (quot_of_quot_of_eq_supp_inj h)

lemma valfield_of_valfield_of_eq_supp_quotient_mk (h : supp v₁ = supp v₂) (r : R) :
  valfield_of_valfield_of_eq_supp h (of $ ideal.quotient.mk _ r) = of (ideal.quotient.mk _ r) :=
begin
  unfold valfield_of_valfield_of_eq_supp,
  rw fraction_ring.map_of,
  rw quot_of_quot_of_eq_supp_quotient_mk',
end

instance (h : supp v₁ = supp v₂) : is_field_hom (valfield_of_valfield_of_eq_supp h) :=
by delta valfield_of_valfield_of_eq_supp; apply_instance

instance (h : supp v₁ = supp v₂) : is_monoid_hom (valfield_of_valfield_of_eq_supp h) :=
is_semiring_hom.is_monoid_hom (valfield_of_valfield_of_eq_supp h)

def valfield_equiv_valfield_of_eq_supp (h : supp v₁ = supp v₂) : valuation_field v₁ ≃r valuation_field v₂ :=
fraction_ring.equiv_of_equiv (quot_equiv_quot_of_eq_supp h)

lemma valfield_equiv_eq_valfield_of_valfield (h : supp v₁ = supp v₂) (q : valuation_field v₁) :
(valfield_equiv_valfield_of_eq_supp h).to_equiv q = valfield_of_valfield_of_eq_supp h q := rfl

instance valfield_equiv.is_field_hom (h : supp v₁ = supp v₂) :
  is_field_hom (valfield_equiv_valfield_of_eq_supp h).to_fun := by apply_instance

lemma valfield_equiv_valfield_mk_eq_mk (h : supp v₁ = supp v₂) (r : R) :
  (valfield_equiv_valfield_of_eq_supp h).to_equiv (of $ ideal.quotient.mk _ r)
  = of (ideal.quotient.mk _ r) :=
valfield_of_valfield_of_eq_supp_quotient_mk h r

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

def val_ring_equiv_of_is_equiv (h : v₁.is_equiv v₂) : v₁.valuation_ring ≃r v₂.valuation_ring :=
{ hom := begin
  cases (valfield_equiv_valfield_of_eq_supp h.supp_eq).hom,
    constructor,
    all_goals {
      intros,
      apply subtype.val_injective,
      apply_assumption,
} end,
..val_ring_equiv_of_is_equiv_aux h }

-- We could prove here
-- lemma val_ring_equiv_mk_eq_mk (h : v₁.is_equiv v₂) (r : R) (hr : v₁ r ≤ 1) :
-- val_ring_equiv_of_is_equiv.to_equiv ⟨of $ ideal.quotient.mk _ r, proof it's in val_ring⟩
-- = ⟨of $ ideal.quotient.mk _ r, longer proof it's in val ring⟩
-- but I'm not sure we need it.

lemma valfeld_le_of_le_of_equiv (h : v₁.is_equiv v₂) (a b : valuation_field v₁) :
  (a ≤ b) ↔ valfield_of_valfield_of_eq_supp (h.supp_eq) a ≤
    valfield_of_valfield_of_eq_supp (h.supp_eq) b :=
is_equiv.on_valuation_field_is_equiv h a b

def valfield.preorder_equiv (h : v₁.is_equiv v₂) :
  preorder_equiv (valuation_field v₁) (valuation_field v₂) :=
{ preorder_iso := valfeld_le_of_le_of_equiv h,
  ..(valfield_equiv_valfield_of_eq_supp h.supp_eq).to_equiv
}

-- units

def valfield_units_of_valfield_units_of_eq_supp (h : supp v₁ = supp v₂) :
  units (valuation_field v₁) → units (valuation_field v₂) :=
units.map $ valfield_of_valfield_of_eq_supp h

instance valfield_units.is_group_hom (h : supp v₁ = supp v₂) :
is_group_hom (valfield_units_of_valfield_units_of_eq_supp h) :=
by unfold valfield_units_of_valfield_units_of_eq_supp; apply_instance

lemma units_valfield_of_units_valfield_of_eq_supp_mk
  (h : supp v₁ = supp v₂) (r : R) (hr : r ∉ supp v₁) :
  valfield_units_of_valfield_units_of_eq_supp h (units_valfield.mk v₁ r hr)
  = units_valfield.mk v₂ r (h ▸ hr) := units.ext $ valfield_equiv_valfield_mk_eq_mk h r

def valfield_units_equiv_units_of_eq_supp (h : supp v₁ = supp v₂) :
group_equiv (units (valuation_field v₁)) (units (valuation_field v₂)) :=
let h' := valfield_equiv_valfield_of_eq_supp h in
by letI := h'.hom; exact units.map_equiv {mul_hom := h'.hom.map_mul, ..h'}
end

lemma valfield_units_equiv_units_mk_eq_mk (h : supp v₁ = supp v₂) (r : R) (hr : r ∉ supp v₁):
(valfield_units_equiv_units_of_eq_supp h).to_equiv (units_valfield.mk v₁ r hr) =
units_valfield.mk v₂ r (h ▸ hr) := units_valfield_of_units_valfield_of_eq_supp_mk h r hr



def valfield_units_preorder_equiv (h : v₁.is_equiv v₂) :
  preorder_equiv (units (valuation_field v₁)) (units (valuation_field v₂)) :=
{ preorder_iso := λ u v, @preorder_equiv.preorder_iso _ _ _ _ (valfield.preorder_equiv h) u.val v.val,
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

lemma val_one_iff_unit_val_one (x : units (valuation_field v))
: x ∈ valuation_field_norm_one v ↔ ((on_valuation_field v) ↑x = 1) :=
begin
  unfold valuation_field_norm_one,
  rw [mem_ker, ←option.some_inj, unit_map_eq],
  refl,
end

lemma is_equiv.norm_one_eq_norm_one (h : is_equiv v₁ v₂) : valuation_field_norm_one v₁ =
  valfield_units_of_valfield_units_of_eq_supp (is_equiv.supp_eq h) ⁻¹'
  valuation_field_norm_one v₂ :=
begin
  ext x,
  rw [set.mem_preimage_eq, val_one_iff_unit_val_one x,
    is_equiv.v_eq_one (is_equiv.on_valuation_field_is_equiv h) x, val_one_iff_unit_val_one],
  refl,
end

-- TODO -- make this a preorder_equiv. This is the heart of the problem
def is_equiv.value_group_equiv_aux (h : is_equiv v₁ v₂) : group_equiv (value_group v₁)
  (quotient_group.quotient
    ((valfield_units_of_valfield_units_of_eq_supp (is_equiv.supp_eq h)) ⁻¹'
      (valuation_field_norm_one v₂))) :=
group_equiv.quot_eq_of_eq $ h.norm_one_eq_norm_one

-- group part of Wedhorn 1.27 (iii) -> (i)
def is_equiv.value_group_equiv (h : is_equiv v₁ v₂) :
group_equiv (value_group v₁) (value_group v₂) :=
group_equiv.trans (h.value_group_equiv_aux) $
  group_equiv.quotient
    (valfield_units_equiv_units_of_eq_supp (is_equiv.supp_eq h)) (valuation_field_norm_one v₂)

-- ordering part of 1.27 (iii) -> (i)
def is_equiv.value_group_order_equiv (h : is_equiv v₁ v₂) (x y : value_group v₁) (h2 : x ≤ y) :
  h.value_group_equiv.to_equiv x ≤ h.value_group_equiv.to_equiv y :=
begin
  induction x, induction y, swap, refl, swap, refl,
  have h3 := (is_equiv.on_valuation_field_is_equiv h x y).1 h2,
  unfold has_le.le preorder.le partial_order.le linear_order.le,
  unfold quotient.lift_on₂',
  unfold quotient.lift_on₂,
  unfold quotient.lift₂,
  unfold quotient.lift,
  dsimp [setoid.r],
  let X : v₂.on_valuation_field (((is_equiv.value_group_equiv h).to_equiv) x)
    ≤ v₂.on_valuation_field (((is_equiv.value_group_equiv h).to_equiv) y) := _,

--  convert h3,
  sorry,
end

end -- section

end valuation

#exit

def is_equiv.value_group_order_equiv (h : is_equiv v₁ v₂) (x y : value_group v₁) (h2 : x ≤ y) :
  h.value_group_equiv.to_equiv x ≤ h.value_group_equiv.to_equiv y :=
begin
  -- ...
  rcases canonical_valuation.value_group.is_ratio v₁ x with ⟨rx, sx, hrx, hsx, hx⟩,
  rcases canonical_valuation.value_group.is_ratio v₁ y with ⟨ry, sy, hry, hsy, hy⟩,
  let cv₁ := canonical_valuation v₁,
  have hsx0 : 0 < cv₁ sx,
  { apply lt_of_not_ge,
    intro hv, apply hsx,
    have hv' : cv₁ sx = 0 := (eq_zero_iff_le_zero cv₁).2 (by rw is_valuation.map_zero cv₁; exact hv),
    exact (eq_zero_iff_le_zero v₁).2
      ((v₁.canonical_valuation_is_equiv sx 0).1 ((eq_zero_iff_le_zero cv₁).1 hv')),
  },
  have hsy0 : 0 < cv₁ sy,
  { apply lt_of_not_ge,
    intro hv, apply hsy,
    have hv' : cv₁ sy = 0 := (eq_zero_iff_le_zero cv₁).2 (by rw is_valuation.map_zero cv₁; exact hv),
    exact (eq_zero_iff_le_zero v₁).2
      ((v₁.canonical_valuation_is_equiv sy 0).1 ((eq_zero_iff_le_zero cv₁).1 hv')),
  },
  have : cv₁ (rx * sy) ≤ cv₁ (ry * sx),
  calc cv₁ (rx * sy) = cv₁ rx * cv₁ sy : cv₁.map_mul _ _
  ...                = (cv₁ sx * x) * cv₁ sy : by rw hx
  ...                = (cv₁ sx * x) * cv₁ sy : by rw hx
  ...                ≤ (cv₁ sx * y) * cv₁ sy :
                         (linear_ordered_comm_monoid.mul_le_mul_right
                           ((linear_ordered_comm_monoid.mul_le_mul_left
                             (with_zero.some_le_some_of_le h2)) _) _)
  ...                = cv₁ sy * y * cv₁ sx : by rw [mul_comm, mul_comm (cv₁ sx), mul_assoc]
  ...                = cv₁ ry * cv₁ sx : by rw hy
  ...                = cv₁ (ry * sx) : (cv₁.map_mul _ _).symm,
  replace this := (v₁.canonical_valuation_is_equiv (rx * sy) (ry * sx)).1 this,
  replace this := (h (rx * sy) (ry * sx)).1 this,
  replace this := (v₂.canonical_valuation_is_equiv (rx * sy) (ry * sx)).2 this,

  -- Goal should now follow from this and a similar calc calculation,
  -- except that we need to know that is_equiv.value_group_equiv sends v1 to v2.

  --induction x,
  --  swap, refl,
  --cases x with x1 x2 h12 h21,
  --dsimp [setoid.r] at h2,
  unfold coe_fn has_coe_to_fun.coe is_equiv.value_group_equiv group_equiv.trans,
  dsimp,
  unfold equiv.trans,
  dsimp,
  unfold is_equiv.value_group_equiv_aux group_equiv.quot_eq_of_eq,
  dsimp,
  rcases canonical_valuation.value_group.is_ratio v₁ x with ⟨rx, sx, hx⟩,
  sorry
end


end -- some random section I guess?

end valuation

/-

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

DEAD CODE

DEAD CODE 1) Old definition of value group.

-- The value group of v is the smallest subgroup Γ_v of Γ for which v takes
-- values in {0} ∪ Γ_v
definition value_group := group.closure {a : Γ | ∃ r : R, v r = some a}

definition value_group_v (v : R → with_zero Γ) [is_valuation v] :=
group.closure ({a : Γ | ∃ r : R, v r = some a})

instance : group (value_group v) :=
@subtype.group _ _ (value_group v) (group.closure.is_subgroup {a : Γ | ∃ r : R, v r = some a})

instance valuation.group_v (v : R → with_zero Γ) [is_valuation v] : group (value_group_v v) :=
  @subtype.group _ _ (value_group_v v) (group.closure.is_subgroup {a : Γ | ∃ r : R, v r = some a})

DEAD CODE 2) Old definition of minimal valuation, now replaced by canonical valuation
[minimal valuation is isomorphic to canonical valuation, but canonical valuation
is a much neater way to do it]

namespace valuation
open quotient_group

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
set_option class.instance_max_depth 69

def of_free_group_aux (r : R) : Γ := option.get_or_else (v r) 1

def of_free_group : multiplicative (R →₀ ℤ) → Γ :=
λ f, finsupp.prod f (λ r n, (of_free_group_aux v r) ^ n)

instance of_free_group.is_group_hom : is_group_hom (of_free_group v) :=
⟨λ f₁ f₂, finsupp.prod_add_index (λ _, rfl) $ λ _ _ _, gpow_add _ _ _⟩

-- This definition helps resolve the set-theoretic issues caused by the
-- fact that the adic spectrum of R is all equivalence classes of
-- valuations, where the value group can vary in an arbitrary universe. It shows
-- that if v : R → {0} ∪ Γ and if R has type Type u₀ then v is equivalent
-- to a valuation taking values in {0} ∪ Γ₀ with Γ₀ also of type u₀.
def minimal_value_group : minimal_valuation.parametrized_subgroup Γ :=
{ Γ     := quotient (is_group_hom.ker (of_free_group v)),
  inc   := ker_lift (of_free_group v),
  hom   := by apply_instance,
  inj   := injective_ker_lift (of_free_group v) }

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
  dsimp [ker_lift, minimal_value_group, minimal_value_group.mk, of_free_group, of_free_group_aux],
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

-- Theorem that valuation v is equivalent to the associated minimal valuation.
lemma minimal_valuation_is_equiv (v : valuation R Γ) :
  v.minimal_valuation.is_equiv v :=
le_of_le (minimal_valuation.map v) (λ g h, iff.refl _)

-- lemma ker_eq_ker_of_equiv (h : v₁.is_equiv v₂) :
--   ker (of_free_group v₁) = ker (of_free_group v₂) :=
-- begin
--   ext f,
--   split; rw [mem_ker, mem_ker]; intro hf,
-- end

-/
