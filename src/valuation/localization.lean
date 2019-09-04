import ring_theory.localization

import valuation.basic

/-!
# Extending valuations to localizations

-/

local attribute [instance] classical.prop_decidable
noncomputable theory

universes u u₀

variables {R : Type u₀} [comm_ring R]
variables {Γ : Type u} [linear_ordered_comm_group Γ]
variables {S : set R} [is_submonoid S]

namespace valuation
open with_zero

variables (v : valuation R Γ)

lemma inverse_exists (s : S) : ∃ u : localization R S, u * s = 1 :=
⟨(localization.to_units s).inv, units.inv_val _⟩

-- I realised later on that I could have used the UMP of rings to give
-- a map localization R S -> K_v and then pulled back the canonical valuation.
-- But I was 80% of the way through the proof it was a valuation when I realised this.
def localization_v (h : ∀ s, s ∈ S → v s ≠ 0) : localization R S → with_zero Γ :=
λ (q : localization R S), quotient.lift_on' q (λ rs, v rs.1 * (v rs.2.1)⁻¹)
  begin
    rintros ⟨r1, s1, hs1⟩,
    rintros ⟨r2, s2, hs2⟩,
    intro hrs,
    dsimp [setoid.r, localization.r] at hrs,
    rcases hrs with ⟨t, ht, hrst⟩,
    rw [add_mul, ←neg_mul_eq_neg_mul, add_neg_eq_zero] at hrst,
    show v r1 * (v s1)⁻¹ = v r2 * (v s2)⁻¹,
    apply with_zero.mul_inv_eq_of_eq_mul (h s1 hs1),
    rw [mul_comm, ←mul_assoc],
    apply with_zero.eq_mul_inv_of_mul_eq (h s2 hs2),
    rw [←v.map_mul, ←v.map_mul, mul_comm],
    apply with_zero.mul_right_cancel (h t ht),
    rw [←v.map_mul, ←v.map_mul, hrst]
  end

lemma localization_is_valuation (h : ∀ s, s ∈ S → v s ≠ 0) : is_valuation (v.localization_v h) :=
{ map_zero := show v 0 * (v 1)⁻¹ = 0, by rw [v.map_zero, zero_mul],
  map_one := show v 1 * (v 1)⁻¹ = 1, by {rw [v.map_one], simp},
  map_mul := λ x y, quotient.induction_on₂' x y begin
    rintro ⟨r1, s1, hs1⟩,
    rintro ⟨r2, s2, hs2⟩,
    -- TODO : I had to write the next line "blind" -- I had to be the compiler.
    -- Am I missing a trick?
    show v (r1 * r2) * (v(s1 * s2))⁻¹ = (v r1 * (v s1)⁻¹) * (v r2 * (v s2)⁻¹),
    have hs12 : s1 * s2 ∈ S := is_submonoid.mul_mem hs1 hs2,
    apply with_zero.mul_inv_eq_of_eq_mul (h (s1 * s2) hs12),
    rw [mul_comm _ (v (s1 * s2)), ←mul_assoc, ←mul_assoc],
    apply with_zero.eq_mul_inv_of_mul_eq (h s2 hs2),
    rw [mul_comm _ (v r2), ←v.map_mul, ←mul_assoc, ←v.map_mul, ←mul_assoc, ←v.map_mul],
    apply with_zero.eq_mul_inv_of_mul_eq (h s1 hs1),
    rw [←v.map_mul],
    apply congr_arg, ring,
  end,
  map_add := λ x y, quotient.induction_on₂' x y begin
    rintro ⟨r1, s1, hs1⟩,
    rintro ⟨r2, s2, hs2⟩,
    show v (s1 * r2 + s2 * r1) * (v (s1 * s2))⁻¹ ≤ v r1 * (v s1)⁻¹ ∨
      v (s1 * r2 + s2 * r1) * (v (s1 * s2))⁻¹ ≤ v r2 * (v s2)⁻¹,
    cases v.map_add (r1 * s2) (r2 * s1) with h1 h2,
    { left,
      apply with_zero.le_mul_inv_of_mul_le (h s1 hs1),
      rw [mul_comm, ←mul_assoc],
      apply with_zero.mul_inv_le_of_le_mul (h (s1 * s2) (is_submonoid.mul_mem hs1 hs2)),
      replace h1 := linear_ordered_structure.mul_le_mul_right h1 (v s1),
      rw [←v.map_mul, ←v.map_mul] at h1 ⊢,
      rw (show s1 * (s1 * r2 + s2 * r1) = (r1 * s2 + r2 * s1) * s1, by ring),
      rwa (show r1 * (s1 * s2) = r1 * s2 * s1, by ring),
    },
    { right,
      apply with_zero.le_mul_inv_of_mul_le (h s2 hs2),
      rw [mul_comm, ←mul_assoc],
      apply with_zero.mul_inv_le_of_le_mul (h (s1 * s2) (is_submonoid.mul_mem hs1 hs2)),
      replace h2 := linear_ordered_structure.mul_le_mul_right h2 (v s2),
      rw [←v.map_mul, ←v.map_mul] at h2 ⊢,
      rw (show s2 * (s1 * r2 + s2 * r1) = (r1 * s2 + r2 * s1) * s2, by ring),
      rwa (show r2 * (s1 * s2) = r2 * s1 * s2, by ring),
    }
  end }

/-- Extension of a valuation to a localization -/
protected def localization (h : ∀ s, s ∈ S → v s ≠ 0) : valuation (localization R S) Γ :=
{ val := v.localization_v h,
  property := v.localization_is_valuation h }

/-- Extension of a valuation to a localization -/
lemma localization_apply (h : ∀ s, s ∈ S → v s ≠ 0) (r : R) :
  (v.localization h : valuation (localization R S) Γ) r = v r :=
show v r * (v 1)⁻¹ = v r, by simp

/-- the extension of a valuation pulls back to the valuation -/
lemma localization_comap (h : ∀ s, s ∈ S → v s ≠ 0) : (v.localization h).comap (localization.of) = v :=
begin
  rw valuation.ext,
  intro r,
  show v r * (v 1)⁻¹ = v r,
  apply with_zero.mul_inv_eq_of_eq_mul (v.map_one_ne_zero),
  rw [v.map_one, mul_one]
end

lemma eq_localization_of_comap_aux {v} (w : valuation (localization R S) Γ)
  (h : w.comap (localization.of) = v) : ∀ s, s ∈ S → v s ≠ 0 := λ s hs h0,
begin
  cases inverse_exists ⟨s, hs⟩ with u hu,
  let s' : units (_root_.localization R S) := ⟨localization.of s, u, mul_comm u s ▸ hu, hu⟩,
--  have hs0 : w (localization.of s) ≠ 0
  cases unit_is_some w s' with γ hγ,
  rw ←h at h0,
  change w s' = 0 at h0,
  rw hγ at h0,
  exact option.no_confusion h0,
end

/-- If a valuation on a localisation pulls back to v then it's the localization of v -/
lemma eq_localization_of_comap (w : valuation (localization R S) Γ)
  (h : w.comap (localization.of) = v) : v.localization (eq_localization_of_comap_aux w h) = w := begin
  rw subtype.ext,
  funext,
  induction q,
  { rcases q with ⟨r, s, hs⟩,
    show v r * (v s)⁻¹ = w (localization.mk r ⟨s, hs⟩),
    rw [localization.mk_eq, ←h, w.map_mul],
    show w r * _ = _,
    congr,
    show (w s)⁻¹ = _,
    have hs0 : w s ≠ 0 := map_unit_ne_zero w  (localization.to_units ⟨s, hs⟩),
    apply with_zero.mul_right_cancel hs0,
    rw ←w.map_mul,
    rw with_zero.mul_left_inv _ hs0,
    rw ←w.map_one, apply congr_arg,
    symmetry,
    exact units.inv_mul _
  },
  refl
end

section fraction_ring
open localization localization.fraction_ring

-- move this def
def integral_domain_of_prime_bot (h : (⊥ : ideal R).is_prime) : integral_domain R :=
{ zero_ne_one := assume zero_eq_one, h.1 $ (ideal.eq_top_iff_one _).mpr $
                 (submodule.mem_bot R).mpr zero_eq_one.symm,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ r s, by { repeat {rw ← submodule.mem_bot R}, apply h.2 },
  .. ‹comm_ring R› }

def integral_domain_of_supp_zero (hv : v.supp = 0) : integral_domain R :=
integral_domain_of_prime_bot $
by { rw [← ideal.zero_eq_bot, ← hv], exact valuation.ideal.is_prime v }

/-- The extension of valuation on R with support 0 to a valuation on the field of fractions. -/
def on_frac (hv : v.supp = 0) : valuation (fraction_ring R) Γ :=
v.localization $ λ r hr hnz,
begin
  letI := v.integral_domain_of_supp_zero hv,
  refine (@mem_non_zero_divisors_iff_ne_zero R _ _ r).mp hr _,
  rwa [← submodule.mem_bot R, ← ideal.zero_eq_bot, ← hv],
end

@[simp] lemma on_frac_comap_eq (hv : supp v = 0) :
  (v.on_frac hv).comap of = v :=
v.localization_comap _

lemma on_frac_comap_eq_apply (hv : supp v = 0) (r : R) :
  ((v.on_frac hv).comap of : valuation R Γ) r = v r := by rw on_frac_comap_eq

/-- Pulling back a valuation on `fraction_ring R` to R and then applying `on_frac` is the
identity function. -/
@[simp] lemma comap_on_frac_eq {R : Type*} [integral_domain R] (v : valuation (fraction_ring R) Γ) :
  (v.comap of).on_frac
  (by {rw [comap_supp, ideal.zero_eq_bot, v.supp.eq_bot_of_prime],
    apply ideal.comap_bot_of_inj, apply fraction_ring.of.injective })
  = v :=
valuation.eq_localization_of_comap _ _ rfl

lemma frac_preorder_comap (hv : supp v = 0) :
  preorder.lift (localization.of) (v.on_frac hv).to_preorder = v.to_preorder :=
preorder.ext $ λ x y, begin show (v.on_frac hv) x ≤ (v.on_frac hv) y ↔ v x ≤ v y,
rw [←on_frac_comap_eq_apply v hv, ←on_frac_comap_eq_apply v hv], exact iff.rfl end

end fraction_ring -- end of section

section valuation_field

/-- The quotient ring R/supp(v) associated to a valuation. -/
definition valuation_ID := (supp v).quotient

/-- the support of a valuation is a prime ideal, so R/supp(v) is an integral domain. -/
instance integral_domain' : integral_domain (valuation_ID v) :=
by delta valuation_ID; apply_instance

/-- The preorder on R/supp(v) induced by Γ via `v.on_quot` -/
instance : preorder (valuation_ID v) := (v.on_quot (le_refl _)).to_preorder

/-- The function R → R/supp(v). -/
def valuation_ID_mk : R → valuation_ID v := ideal.quotient.mk (supp v)

/-- The function R → R/supp(v) is a ring homomorphism. -/
instance : is_ring_hom (v.valuation_ID_mk) := by unfold valuation_ID_mk; apply_instance

/-- The kernel of R → R/supp(v) is supp(v). -/
lemma valuation_ID_mk_ker (r : R) : v.valuation_ID_mk r = 0 ↔ r ∈ supp v :=
ideal.quotient.eq_zero_iff_mem

/-- `valuation_field v` is the field of fractions of R/supp(v). -/
definition valuation_field := localization.fraction_ring (valuation_ID v)

/-- The field of fractions of R/supp(v) is a field. -/
instance : discrete_field (valuation_field v) := by delta valuation_field; apply_instance

/-- The canonical map R → fraction_ring (R/supp(v)). -/
def valuation_field_mk (r : R) : valuation_field v := localization.of (v.valuation_ID_mk r)

/-- The map R → Frac(R/supp(v)) is a ring homomorphism. -/
instance to_valuation_field.is_ring_hom : is_ring_hom (valuation_field_mk v) :=
by delta valuation_field_mk; apply_instance

/-- The kernel of R → Frac(R/supp(v)) is supp(v). -/
lemma valuation_field_mk_ker (r : R) : v.valuation_field_mk r = 0 ↔ r ∈ supp v :=
⟨λ h, (v.valuation_ID_mk_ker r).1 $ localization.fraction_ring.eq_zero_of _ h,
 λ h, show localization.of _ = 0, by rw (v.valuation_ID_mk_ker r).2 h; apply is_ring_hom.map_zero⟩

lemma valuation_field_mk_ne_zero (r : R) (hr : v r ≠ 0) : valuation_field_mk v r ≠ 0 :=
λ h, hr ((valuation_field_mk_ker v r).1 h)

/-- The induced preorder on Frac(R/supp(v)). -/
instance valfield_preorder : preorder (valuation_field v) :=
  ((v.on_quot (le_refl _)).on_frac $ quot_supp_zero v).to_preorder

/-- The induced map from R \ supp(v) to the units of Frac(R/supp(v)). -/
def units_valfield_mk (r : R) (h : r ∉ supp v) : units (valuation_field v) :=
⟨v.valuation_field_mk r,
 (v.valuation_field_mk r)⁻¹,
 mul_inv_cancel (λ h2, h $ ideal.quotient.eq_zero_iff_mem.1 $
   localization.fraction_ring.eq_zero_of _ h2),
 inv_mul_cancel (λ h2, h $ ideal.quotient.eq_zero_iff_mem.1 $
   localization.fraction_ring.eq_zero_of _ h2)⟩

/-- The preorder on the units of Frac(R/supp(v)) induced by the extension of v. -/
instance units_valfield_preorder :
  preorder (units (valuation_field v)) := preorder.lift (λ u, u.val) (by apply_instance)

-- TODO -- on_frac_quot_comap_eq got deleted; it was never used. Can we delete this instance?

-- on_frac_quot_comap_eq needs more class.instance_max_depth to compile if
-- this instance is not explicitly given as a hint
instance : is_submonoid (localization.non_zero_divisors (ideal.quotient (supp v))) :=
by apply_instance

/-- The valuation on Frac(R/supp(v)) induced by v. -/
definition on_valuation_field : valuation (valuation_field v) Γ :=
on_frac (v.on_quot (set.subset.refl _))
begin
  rw [supp_quot_supp, ideal.zero_eq_bot],
  apply ideal.map_quotient_self,
end

/-- `valuation_ring v` is the elements of Frac(R/supp(v)) whose valuation is at most 1. -/
definition valuation_ring := {x | v.on_valuation_field x ≤ 1}

/-- `valuation_ring v` is a subring of Frac(R/supp(v)). -/
instance : is_subring (valuation_ring v) :=
{ zero_mem := show v.on_valuation_field 0 ≤ 1, by simp,
  add_mem := λ x y hx hy,
  by cases (v.on_valuation_field.map_add x y) with h h;
    exact le_trans h (by assumption),
  neg_mem := by simp [valuation_ring],
  one_mem := by simp [valuation_ring, le_refl],
  mul_mem := λ x y (hx : _ ≤ _) (hy : _ ≤ _), show v.on_valuation_field _ ≤ 1,
  by convert le_trans (linear_ordered_structure.mul_le_mul_left hy _) _; simp [hx] }

/-- `max_ideal v` is the ideal of `valuation_ring v` consisting of things with valuation
strictly less than 1. -/
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
    convert (linear_ordered_structure.mul_le_mul_right _ _),
    exact map_mul _ _ _,
    swap,
    convert c.property,
    simpa using hx
  end }

set_option class.instance_max_depth 40

/-- `max_ideal v` is indeed a maximal ideal of `valuation_ring v`. -/
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

/-- `residue_field v` is the quotient of `valuation_ring v` by `max_ideal v`. -/
definition residue_field := (max_ideal v).quotient

/-- `residue_field v` is a field. -/
instance residue_field.discrete_field : discrete_field (residue_field v) := ideal.quotient.field _
end valuation_field
end valuation
