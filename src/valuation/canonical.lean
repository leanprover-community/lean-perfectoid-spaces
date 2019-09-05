import for_mathlib.quotient_group

import valuation.localization

/-! valuation.canonical

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
_canonical valuation_ associated to v; this valuation is equivalent to v.
A technical advantage that this valuation has from the point of view
of Lean's type theory is that if R is in universe u₁ and Γ in universe u₂,
then v : valuation R Γ will be in universe `max u₁ u₂` but the canonical
valuation will just be in universe u₁. In particular, if v and v' are equivalent
then their associated canonical valuations are isomorphic and furthermore in the
same universe.

All of the below names are in the `valuation` namespace.

`value_group v` is the totally ordered group K^*/A^* (note that it is
isomorphic to the subgroup of Γ which Wedhorn calls the value group in [W; 1.22]), and
`value_group.to_Γ` is the group homomorphism to \Gamma.
`canonical_valuation v` is the canonical valuation.
`canonical_valuation.to_Γ v` is the lemma that says that we can
recover v from `canonical_valuation v` using the group homomorphism
from K^*/A^* to Γ.

-- TODO -- rewrite this when I've remembered what we proved.
We then prove some of Proposition-and-Definition 1.27 of Wedhorn,
where we note that we used (iii) for the definition, and
we're now using a different definition to Wedhorn for the value group
(because it's isomorphic so no mathematician will care, and
it's easier for us because it's in a smaller universe).

-/

local attribute [instance] classical.prop_decidable
noncomputable theory

universes u u₀ u₁ u₂ u₃

variables {R : Type u₀} [comm_ring R]

namespace valuation

variables {Γ : Type u} [linear_ordered_comm_group_with_zero Γ]
variables (v : valuation R Γ)

/-- The elements of `units (valuation_field v)` with norm 1. -/
definition valuation_field_norm_one :=
is_group_hom.ker (units.map v.on_valuation_field.to_monoid_hom)

/-- `valuation_field_norm_one v is a normal subgroup of `units (valuation_field v)`. -/
instance (v : valuation R Γ) : normal_subgroup (valuation_field_norm_one v) :=
by unfold valuation_field_norm_one; apply_instance

namespace value_group

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

end value_group

section canonical_equivalent_valuation

/-- The value group of the canonical valuation.-/
def value_group (v : valuation R Γ) : Type u₀ :=
@quotient v.valuation_field (value_group.setoid v)

/-- The natural quotient map from `units (valuation_field v)` to `value_group v`. -/
def value_group.mk (v : valuation R Γ) :
  valuation_field v → value_group v :=
quotient.mk'

def value_group_aux (v : valuation R Γ) : Type u₀ :=
quotient_group.quotient (valuation_field_norm_one v)

def value_group_aux_to_value_group : v.value_group_aux → v.value_group :=
λ x, quotient.lift_on' x (λ u, value_group.mk v u) $
by { intros a b h, exact quotient.sound' ⟨_, h, a.mul_inv_cancel_left b⟩ }

/- The priorities of the next two instances are lower than the default so that
  the `linear_ordered_comm_group` instance below is found first. If these are found first,
  it will cause timeouts during type class inference. -/
@[priority 100] instance value_group.comm_group : comm_group (value_group v) :=
by dunfold value_group; apply_instance

@[priority 100] instance value_group.linear_order : linear_order (value_group v) :=
{ le := λ a' b',
    quotient.lift_on₂' a' b' (λ s t, v.on_valuation_field ↑s ≤ v.on_valuation_field ↑t) $
    λ a b c d hac hbd, begin
      change a⁻¹ * c ∈ is_group_hom.ker _ at hac,
      change b⁻¹ * d ∈ is_group_hom.ker _ at hbd,
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

/-- The natural quotient map from `units (valuation_field v)` to `value_group v`
is a group homomorphism. -/
instance value_group_quotient.is_group_hom :
is_group_hom (value_group_quotient v) := is_group_hom.mk' $ λ _ _, rfl

/-- `value_group v` is a linearly ordered commutative group. -/
instance : linear_ordered_comm_group (value_group v) :=
{ mul_le_mul_left := begin rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩,
    change v.on_valuation_field a ≤ v.on_valuation_field b at h,
    change value_group_quotient v c * value_group_quotient v a
    ≤ value_group_quotient v c * value_group_quotient v b,
    rw ←is_mul_hom.map_mul (value_group_quotient v),
    rw ←is_mul_hom.map_mul (value_group_quotient v),
    change v.on_valuation_field (c * a) ≤ v.on_valuation_field (c * b),
    rw v.on_valuation_field.map_mul,
    rw v.on_valuation_field.map_mul,
    exact with_zero.mul_le_mul_left _ _ h _
end,
 ..value_group.comm_group v,
 ..value_group.linear_order v }

/-- The natural map `value_group v → Γ` induced by v. -/
def value_group.to_Γ (v : valuation R Γ) :
value_group v → Γ :=
quotient_group.lift (valuation_field_norm_one v) v.on_valuation_field.unit_map $
  λ x, (is_group_hom.mem_ker _).1

/-- The natural map `value_group v → Γ` is a group homomorphism. -/
instance : is_group_hom (value_group.to_Γ v) :=
by unfold value_group.to_Γ; apply_instance

/-- The natural map `value_group v → Γ` preserves ≤ -/
lemma value_group.to_Γ_monotone :
  monotone (value_group.to_Γ v) :=
begin
  rintros ⟨x⟩ ⟨y⟩,
  erw [mk_le_mk_iff, ← unit_map_eq, ← unit_map_eq, with_bot.some_le_some],
  exact id,
end

/-- The natural map `value_group v → Γ` is injective. -/
lemma value_group.to_Γ_injective :
  function.injective (value_group.to_Γ v) :=
quotient_group.injective_ker_lift _

/-- The natural map `value_group v → Γ` preserves <. -/
lemma value_group.to_Γ_strict_mono :
  strict_mono (value_group.to_Γ v) :=
strict_mono_of_monotone_of_injective
  (value_group.to_Γ_monotone _)
  (value_group.to_Γ_injective _)

-- The canonical valuation associated to v is the obvious map
-- from R to value_group v := Frac(R/supp(v)) / A^*
-- (thought of as K^*/A^* union 0)

/-- The underlying function of the natural valuation on Frac(R/supp(v)) taking
values in {0} ∪ `value_group v` -/
definition valuation_field.canonical_valuation_v :
valuation_field v → with_zero (value_group v) :=
λ k, if h : (k = 0) then 0 else
  value_group_quotient v ⟨k,k⁻¹,mul_inv_cancel h, inv_mul_cancel h⟩

/-- The valuation Frac(R/supp(v)) → {0} ∪ `value_group v` is a valuation. -/
lemma valuation_field.canonical_valuation_v.is_valuation :
is_valuation (valuation_field.canonical_valuation_v v) :=
{ map_zero := dif_pos rfl,
  map_one := begin unfold valuation_field.canonical_valuation_v, rw dif_neg zero_ne_one.symm,
    apply option.some_inj.2,
    convert is_group_hom.map_one (value_group_quotient v),
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
    show value_group_quotient v {val := x * y, inv := (x * y)⁻¹, val_inv := _, inv_val := _} =
      value_group_quotient v {val := x * y, inv := _, val_inv := _, inv_val := _},
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

/-- The canonical valuation on Frac(R/supp(v)), taking values in `value_group v`. -/
def valuation_field.canonical_valuation :
valuation (valuation_field v) (value_group v) :=
⟨valuation_field.canonical_valuation_v v, valuation_field.canonical_valuation_v.is_valuation v⟩

lemma valuation_field.canonical_valuation_unit :
unit_map (valuation_field.canonical_valuation v) = value_group_quotient v :=
begin
  -- one has to really dig to get to the `if`
  ext x,
  rw ←option.some_inj,
  rw unit_map_eq,
  show dite (x.val = 0) (λ (_x : x.val = 0), (0 : with_zero (value_group v)))
      (λ (h : ¬x.val = 0),
        (value_group_quotient v {val := ↑x, inv := (↑x)⁻¹, val_inv := _, inv_val := _})) =
    some (value_group_quotient v x),
  -- The `if` is now accessible for `split_ifs`.
  split_ifs with h,
  { change x.val = 0 at h,
    have h2 := x.val_inv,
    rw [h, zero_mul] at h2,
    exfalso, revert h2,
    simp },
  { show some _ = some _,
    congr,
    apply units.ext,
    refl }
end

/-- The canonical valuation on R/supp(v), taking values in `value_group v`. -/
definition quotient.canonical_valuation (v : valuation R Γ) :
  valuation (ideal.quotient (supp v)) (value_group v) :=
@comap _ _ _ _ (valuation_field.canonical_valuation v) _ _ (localization.of)
  (by apply_instance)

/-- The canonical valuation on R, taking values in `value_group v`. -/
definition canonical_valuation (v : valuation R Γ) :
  valuation R (value_group v) :=
comap (quotient.canonical_valuation v) (ideal.quotient.mk (supp v))

/-- The relation between `v.canonical_valuation r` and `v r`. -/
lemma canonical_valuation_eq (v : valuation R Γ) (r : R) : v.canonical_valuation r =
  if h : (v.valuation_field_mk r = 0) then 0 else
         some (value_group_quotient v
              {val := v.valuation_field_mk r,
               inv := (v.valuation_field_mk r)⁻¹,
               val_inv := mul_inv_cancel h,
               inv_val := inv_mul_cancel h})
   := rfl

lemma canonical_valuation_not_mem_supp_eq (v : valuation R Γ) (r : R) (hr : r ∉ supp v) :
  v.canonical_valuation r = some (value_group_quotient v (units_valfield_mk v r hr)) :=
begin
  rw canonical_valuation_eq,
  split_ifs, swap, refl,
  exfalso,
  apply hr,
  exact (v.valuation_field_mk_ker r).1 h
end

end canonical_equivalent_valuation -- end of section

namespace canonical_valuation

-- This looks handy to know but we never actually use it.
/-- Every element of `value_group v` is a ratio of things in the image of `canonical_valuation v`.-/
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
  rw ←(value_group_quotient.is_group_hom v).map_mul,
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

/-- v can be reconstructed from `canonical_valuation v` by pushing forward along
the map `value_group v → Γ`. -/
lemma to_Γ :
  (canonical_valuation v).map (value_group.to_Γ v) (value_group.to_Γ_monotone v) = v :=
begin
  rw valuation.ext_iff,
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
  { intros g hr,
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
    rw [unit_map_eq, ←hr],
    show (on_valuation_field v) (r'') = v r,
    exact localization_apply _ _ _, }
end

end canonical_valuation -- end of namespace

end valuation -- end of namespace

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
  convert is_equiv_of_map_strict_mono
    (value_group.to_Γ v)
    (value_group.to_Γ_strict_mono _),
  symmetry,
  exact canonical_valuation.to_Γ v,
end

namespace is_equiv

-- Various lemmas about valuations being equivalent.

variables {v : valuation R Γ} {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} {v₃ : valuation R Γ₃}

/-- If J ⊆ supp(v) then pulling back the induced valuation on R / J back to R gives a
valuation equivalent to v. -/
lemma on_quot_comap_self {J : ideal R} (hJ : J ≤ supp v) :
  is_equiv ((v.on_quot hJ).comap (ideal.quotient.mk J)) v :=
of_eq (on_quot_comap_eq _ _)

/-- Two valuations on R/J are equivalent iff their pullbacks to R are equivalent. -/
lemma comap_on_quot (J : ideal R) (v₁ : valuation J.quotient Γ₁) (v₂ : valuation J.quotient Γ₂) :
  (v₁.comap (ideal.quotient.mk J)).is_equiv (v₂.comap (ideal.quotient.mk J)) ↔ v₁.is_equiv v₂ :=
{ mp  := begin rintros h ⟨x⟩ ⟨y⟩, exact h x y end,
  mpr := λ h, comap _ h }

open localization

/-- If supp(v)=0 then v is equivalent to the pullback of the extension of v to Frac(R). -/
lemma on_frac_comap_self {R : Type u₀} [integral_domain R] (v : valuation R Γ) (hv : supp v = 0) :
  is_equiv ((v.on_frac hv).comap of) v :=
of_eq (on_frac_comap_eq v hv)

/-- If R is an ID then two valuations on R are equivalent iff their extensions to Frac(R) are
equivalent. -/
lemma comap_on_frac {R : Type u₀} [integral_domain R]
(v₁ : valuation (fraction_ring R) Γ₁) (v₂ : valuation (fraction_ring R) Γ₂) :
  (v₁.comap of).is_equiv (v₂.comap of) ↔ is_equiv v₁ v₂ :=
{ mp  := begin
    rintros h ⟨x⟩ ⟨y⟩,
    erw ← comap_on_frac_eq v₁,
    erw ← comap_on_frac_eq v₂,
    repeat {erw with_zero.div_le_div},
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
  mpr := λ h, comap _ h }

/-- [Wed 1.27] (iii) -> first part of (ii). -/
lemma supp_eq (h : v₁.is_equiv v₂) : supp v₁ = supp v₂ :=
ideal.ext $ λ r,
calc r ∈ supp v₁ ↔ v₁ r = 0    : mem_supp_iff' _ _
             ... ↔ v₁ r ≤ v₁ 0 : eq_zero_iff_le_zero _
             ... ↔ v₂ r ≤ v₂ 0 : h r 0
             ... ↔ v₂ r = 0    : (eq_zero_iff_le_zero _).symm
             ... ↔ r ∈ supp v₂ : (mem_supp_iff' _ _).symm

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
lemma canonical_valuation_supp (v : valuation R Γ) :
  supp (v.canonical_valuation) = supp v := (canonical_valuation_is_equiv v).supp_eq

section Wedhorn1_27_equivalences

variables {v : valuation R Γ} {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} {v₃ : valuation R Γ₃}

open is_group_hom quotient_group function

-- We now start on the equivalences of Wedhorn 1.27. The first one is easy.

/-- Wedhorn 1.27 (i) → (iii) : An ordered isomorphism of value groups which commutes with
canonical valuations implies that valuations are equivalent. -/
lemma of_inj_value_group (f : v₁.value_group → v₂.value_group)
[is_group_hom f] (hf : strict_mono f)
(H : v₂.canonical_valuation = v₁.canonical_valuation.map f (hf.monotone)) :
  v₁.is_equiv v₂ :=
begin
  refine (v₁.canonical_valuation_is_equiv.symm).trans _,
  refine (is_equiv.trans _ (v₂.canonical_valuation_is_equiv)),
  rw H,
  symmetry,
  exact is_equiv_of_map_strict_mono _ _
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
def quot_equiv_quot_of_eq_supp (h : supp v₁ = supp v₂) : valuation_ID v₁ ≃r valuation_ID v₂ :=
{ hom :=quot_of_quot_of_eq_supp.is_ring_hom h,
  ..valuation_ID.equiv h}

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
  valuation_field v₁ ≃r valuation_field v₂ :=
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
  (comap (v₂.on_quot (set.subset.refl _)) (quot_of_quot_of_eq_supp h.supp_eq)) :=
begin
  rw [← is_equiv.comap_on_quot, ← comap_comp],
  simp [h],
end

/-- If v₁ and v₂ are equivalent then the induced valuations on Frac(R/supp(v₁)) and
Frac(R/supp(v₂)) [pulled back] are equivalent. -/
lemma is_equiv.on_valuation_field_is_equiv (h : v₁.is_equiv v₂) :
  v₁.on_valuation_field.is_equiv
  (comap v₂.on_valuation_field (valfield_of_valfield_of_eq_supp h.supp_eq)) :=
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

-- we omit the proof that the diagram {r | v₁ r ≤ 1} → v₁.valuation_ring → v₂.valuation_ring
-- commutes.

lemma valfield_le_of_le_of_equiv (h : v₁.is_equiv v₂) (a b : valuation_field v₁) :
  (a ≤ b) ↔ valfield_of_valfield_of_eq_supp (h.supp_eq) a ≤
    valfield_of_valfield_of_eq_supp (h.supp_eq) b :=
is_equiv.on_valuation_field_is_equiv h a b

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
mul_equiv (units (valuation_field v₁)) (units (valuation_field v₂)) :=
let h' := valfield_equiv_valfield_of_eq_supp h in
by letI := h'.hom; exact units.map_equiv {map_mul' := h'.hom.map_mul, ..h'}

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

lemma val_one_iff_unit_val_one (x : units (valuation_field v))
: x ∈ valuation_field_norm_one v ↔ ((on_valuation_field v) ↑x = 1) :=
begin
  unfold valuation_field_norm_one,
  rw [mem_ker, ←option.some_inj, unit_map_eq],
  refl,
end

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
  mul_equiv (value_group v₁) (value_group v₂) :=
mul_equiv.quotient (valfield_units_equiv_units_of_eq_supp h.supp_eq) (valuation_field_norm_one v₁)
  (valuation_field_norm_one v₂) (is_equiv.norm_one_eq_norm_one h : _)

lemma value_mul_equiv_units_mk_eq_mk (h : is_equiv v₁ v₂) (r : R) (hr : r ∉ supp v₁) :
  (h.value_mul_equiv) (value_group_quotient v₁ (units_valfield_mk v₁ r hr)) =
  value_group_quotient v₂ (units_valfield_mk v₂ r (h.supp_eq ▸ hr)) :=
begin
  rw ←valfield_units_equiv_units_mk_eq_mk (h.supp_eq) r hr,
  refl,
end

def is_equiv.with_zero_value_mul_equiv (h : is_equiv v₁ v₂) :
  (with_zero (value_group v₁)) ≃* (with_zero (value_group v₂)) :=
 h.value_mul_equiv.to_with_zero_mul_equiv

-- ordering part of 1.27 (iii) -> (i)
def is_equiv.value_group_order_equiv_aux (h : is_equiv v₁ v₂) (x y : value_group v₁) (h2 : x ≤ y) :
  h.value_mul_equiv x ≤ h.value_mul_equiv y :=
begin
  induction x with x, induction y, swap, refl, swap, refl,
  exact (is_equiv.on_valuation_field_is_equiv h x y).1 h2,
end

def is_equiv.value_group_le_equiv (h : is_equiv v₁ v₂) :
  (value_group v₁) ≃≤ (value_group v₂) :=
{ le_map := λ x y, linear_order_le_iff_of_monotone_injective
  (h.value_mul_equiv.to_equiv.bijective.1)
  (is_equiv.value_group_order_equiv_aux h) x y
   ..h.value_mul_equiv}

def is_equiv.value_mul_equiv_monotone (h : is_equiv v₁ v₂) :
  monotone (h.value_mul_equiv) := λ x y,
  (@@le_equiv.le_map _ _ (is_equiv.value_group_le_equiv h)).1

def is_equiv.with_zero_value_group_le_equiv (h : is_equiv v₁ v₂) :
  (with_zero (value_group v₁)) ≃≤ (with_zero (value_group v₂)) :=
preorder_equiv.to_with_zero_preorder_equiv h.value_group_le_equiv

def is_equiv.with_zero_value_group_lt_equiv (h : is_equiv v₁ v₂) :
  (with_zero (value_group v₁)) ≃< (with_zero (value_group v₂)) :=
preorder_equiv.to_lt_equiv h.with_zero_value_group_le_equiv

lemma is_equiv.with_zero_value_mul_equiv_mk_eq_mk (h : v₁.is_equiv v₂) (r : R) :
  with_zero.map h.value_mul_equiv (canonical_valuation v₁ r) =
  canonical_valuation v₂ r :=
begin
  by_cases h1 : (r ∈ supp v₁),
  { -- zero case
    have hs1 : r ∈ supp (canonical_valuation v₁) := by rwa v₁.canonical_valuation_supp,
    have hs2 : r ∈ supp (canonical_valuation v₂),
      rwa is_equiv.supp_eq h.canonical_equiv_of_is_equiv at hs1,
    rw (mem_supp_iff _ r).1 hs1,
    rw (mem_supp_iff _ r).1 hs2,
    refl,
  },
  { -- not in supp case
    have h2 : r ∉ supp v₂ := by rwa ←h.supp_eq,
    rw v₁.canonical_valuation_not_mem_supp_eq _ h1,
    rw v₂.canonical_valuation_not_mem_supp_eq _ h2,
    show some _ = some _, congr,
    exact value_mul_equiv_units_mk_eq_mk h r h1,
  }
end

end Wedhorn1_27_equivalences -- section

end valuation
