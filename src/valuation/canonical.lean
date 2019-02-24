import valuation.basic

/-

The purpose of this file is to define a "canonical" valuation equivalent to
a given valuation. If v : R → Γ ∪ {0} is an arbitray valuation,
then v extends to a valuation on K = Frac(R/supp(v)) and hence to a group
homomorphism K^* → Γ, whose kernel is A^*, the units in the valuation ring
(or equivalently the things in K^* of norm at most 1). This embeds K^*/A^*
into Γ and hence gives it the structure of a linearly ordered commutative group.
There is an induced map R → (K^*/A^*) ∪ {0}, the canonical valuation
associated to v, and this valuation is equivalent to v.

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
set_option class.instance_max_depth 69

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
