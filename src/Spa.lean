import ring_theory.localization
import ring_theory.subring
import continuous_valuations
import Huber_pair
import Huber_ring.localization

import for_mathlib.nonarchimedean.basic
import for_mathlib.data.set.finite
import for_mathlib.uniform_space.ring -- need completions of rings plus UMP
import for_mathlib.group -- some stupid lemma about units

universes u₁ u₂ u₃

local attribute [instance, priority 0] classical.prop_decidable

open set function Spv valuation

variables {Γ : Type*} [linear_ordered_comm_group Γ]

-- Wedhorn def 7.23.
definition Spa (A : Huber_pair) : set (Spv A) :=
{v | v.is_continuous ∧ ∀ r ∈ A⁺, v r ≤ 1}

lemma mk_mem_Spa {A : Huber_pair} {v : valuation A Γ} :
  mk v ∈ Spa A ↔ v.is_continuous ∧ ∀ r ∈ A⁺, v r ≤ 1 :=
begin
  apply and_congr,
  { apply is_equiv.is_continuous_iff,
    apply out_mk, },
  { apply forall_congr,
    intro r,
    apply forall_congr,
    intro hr,
    convert (out_mk v) r 1;
    rw [valuation.map_one] }
end

namespace Spa

variable {A : Huber_pair}

instance : has_coe (Spa A) (Spv A) := ⟨subtype.val⟩

definition basic_open (r s : A) : set (Spa A) :=
{v | v r ≤ v s ∧ v s ≠ 0 }

lemma mk_mem_basic_open {r s : A} {v : valuation A Γ} {hv : mk v ∈ Spa A} :
(⟨mk v, hv⟩ : Spa A) ∈ basic_open r s ↔ v r ≤ v s ∧ v s ≠ 0 :=
begin
  apply and_congr,
  { apply out_mk, },
  { apply (out_mk v).ne_zero, },
end

instance (A : Huber_pair) : topological_space (Spa A) :=
topological_space.generate_from {U : set (Spa A) | ∃ r s : A, U = basic_open r s}

lemma basic_open.is_open (r s : A) : is_open (basic_open r s) :=
topological_space.generate_open.basic (basic_open r s) ⟨r, s, rfl⟩

lemma basic_open_eq (s : A) : basic_open s s = {v | v s ≠ 0} :=
set.ext $ λ v, ⟨λ h, h.right, λ h, ⟨le_refl _, h⟩⟩

-- should only be applied with (Hfin : fintype T) and (Hopen: is_open (span T))
definition rational_open (s : A) (T : set A) : set (Spa A) :=
{v | (∀ t ∈ T, (v t ≤ v s)) ∧ (v s ≠ 0)}

-- Here's everything in one package.
structure rational_open_data (A : Huber_pair) :=
(s : A)
(T : set A)
(Tfin : fintype T)
(Hopen : is_open ((ideal.span T) : set A))

instance (r : rational_open_data A) : fintype r.T := r.Tfin

namespace rational_open_data

def ext (r₁ r₂ : rational_open_data A) (hs : r₁.s = r₂.s) (hT : r₁.T = r₂.T) :
  r₁ = r₂ :=
begin
  cases r₁, cases r₂,
  congr; assumption
end

def rational_open (r : rational_open_data A) : set (Spa A) :=
rational_open r.s r.T

def localization (r : rational_open_data A) := Huber_ring.away r.T r.s

instance (r : rational_open_data A) : topological_space (localization r) :=
Huber_ring.away.topological_space r.T r.s r.Hopen

instance (r : rational_open_data A) : ring_with_zero_nhd (localization r) :=
Huber_ring.away.ring_with_zero_nhd r.T r.s r.Hopen

instance (r : rational_open_data A) : comm_ring (localization r) :=
by unfold localization; apply_instance

instance (r : rational_open_data A) : topological_ring (localization r) := by apply_instance

open algebra

instance (r : rational_open_data A) : algebra A (localization r) := Huber_ring.away.algebra r.T r.s

/- In this file, we are going to take a projective limit over a preordered set of rings,
   to make a presheaf. The underlying type of this preorder is `rational_open_data A`.

 The correct preorder on rational open data:

def correct_preorder : preorder (rational_open_data A) :=
{ le := λ r1 r2, rational_open r1 ⊆ rational_open r2,
  le_refl := λ _ _, id,
  le_trans := λ _ _ _, subset.trans,
}

One can prove (in maths) that r1 ≤ r2 iff there's a continuous R-algebra morphism
of Huber pairs localization r2 → localization r1. I think the ← direction of this
iff is straightforward (but I didn't think about it too carefully). However we
definitely cannot prove the → direction of this iff in this repo yet because we
don't have enough API for cont. Here is an indication
of part of the problem. localization r2 is just A[1/r2.s]. But we cannot prove yet r2.s is
invertible in localization.r1, even though we know it doesn't canish anywhere on
rational_open r2 and hence on rational_open r1, because the fact that it doesn't vanish anywhere
on rational_open r1 only means that it's not in any prime ideal corresponding
to a *continuous* valuation on localization r1; one would now need to prove that every maximal ideal
is the support of a continuous valuation, which is Wedhorn 7.52(2). This is not
too bad -- but it is work that we have not yet done. This is not the whole story though;
we would also need that r1.T is power-bounded in localization.r2
and this looks worse: it's Wedhorn 7.52(1). Everything is do-able, but it's just *long*.
Long as in "thousands more lines of code".

We have to work with a weaker preorder then, because haven't made a good enough
API for continuous valuations. We basically work with the preorder r1 ≤ r2 iff
there's a continuous R-algebra map localization r2 → localization r1, i.e, we
define our way around the problem. We are fortunate in that we can prove
(in maths) that the projective limit over this preorder agrees with the projective
limit over the correct preorder.
-/

-- note: I don't think we ever use le_refl or le_trans
instance : preorder (rational_open_data A) :=
{ le := λ r1 r2, ∃ k : A, r1.s * k = r2.s ∧
    ∀ t₁ ∈ r1.T, ∃ t₂ ∈ r2.T, ∃ N : ℕ, r2.s ^ N * t₂ = r2.s ^ N * (t₁ * k),
  le_refl := λ r, ⟨1, mul_one _, λ t ht, ⟨t, ht, 0, by rw mul_one⟩⟩,
  le_trans := λ a b c ⟨k, hk, hab⟩ ⟨l, hl, hbc⟩, ⟨k * l, by rw [←mul_assoc, hk, hl],
    λ ta hta, begin
      rcases hab ta hta with ⟨tb, htb, Nab, h1⟩,
      rcases hbc tb htb with ⟨hc, htc, Nbc, h2⟩,
      use hc, use htc, use (Nab + Nbc),
      rw [←mul_assoc, pow_add, mul_assoc, h2, ←hl, mul_pow, mul_pow],
      rw (show b.s ^ Nab * l ^ Nab * (b.s ^ Nbc * l ^ Nbc * (tb * l)) =
        b.s ^ Nab * tb * (l ^ Nab * (b.s ^ Nbc * l ^ Nbc *  l)), by ring),
      rw h1,
      ring
    end⟩
}

-- our preorder is weaker than the preorder we're supposed to have but don't. However
-- the projective limit we take over our preorder is provably (in maths) equal to
-- the projective limit that we cannot even formalise. The thing we definitely need
-- is that if r1 ≤ r2 then there's a map localization r1 → localization r2

/-- This awful function produces r1.s as a unit in localization r2 -/
noncomputable def s_inv_aux (r1 r2 : rational_open_data A) (h : r1 ≤ r2) : units (localization r2) :=
@units.unit_of_mul_left_eq_unit _ _
  ((of_id A (localization r2)).to_fun r1.s)
  ((of_id A (localization r2)).to_fun (classical.some h))
  (localization.to_units (⟨r2.s, 1, by simp⟩ : powers r2.s)) (begin
    suffices : (of_id A (localization r2)).to_fun (r1.s * classical.some h) =
      (localization.to_units (⟨r2.s, 1, by simp⟩ : powers r2.s)).val,
      convert this,
      convert (is_ring_hom.map_mul _).symm,
      apply_instance, -- stupid type class inference
    rw (classical.some_spec h).1,
    refl,
end)

noncomputable def rational_open_subset.restriction {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  localization r1 → localization r2 :=
Huber_ring.away.lift r1.T r1.s
( show ((s_inv_aux r1 r2 h)⁻¹).inv = (of_id A (localization r2)).to_fun r1.s, from rfl)

def localization.nonarchimedean (r : rational_open_data A) :
  topological_add_group.nonarchimedean (localization r) :=
of_submodules_comm.nonarchimedean

section
open localization submodule Huber_ring.away
local attribute [instance] set.pointwise_mul_comm_semiring
local attribute [instance] set.mul_action

def localization.power_bounded_data (r : rational_open_data A) : set (localization r) :=
let s_inv : localization r := ((to_units ⟨r.s, ⟨1, by simp⟩⟩)⁻¹ : units (localization r)) in
(s_inv • of_id A (localization r) '' r.T)

set_option class.instance_max_depth 50

theorem localization.power_bounded (r : rational_open_data A) :
  is_power_bounded_subset (localization.power_bounded_data r) :=
begin
  apply bounded.subset,
  work_on_goal 0 { apply add_group.subset_closure },
  show is_bounded (ring.closure (localization.power_bounded_data r)),
  intros U hU,
  rw of_submodules_comm.nhds_zero at hU,
  cases hU with V hV,
  refine ⟨_, mem_nhds_sets (of_submodules_comm.is_open V) _, _⟩,
  { rw submodule.mem_coe,
    exact submodule.zero_mem _ },
  { intros v hv b hb,
    apply hV,
    rw mul_comm,
    rw submodule.mem_coe at hv ⊢,
    convert submodule.smul_mem _ _ hv,
    work_on_goal 1 { exact ⟨b, hb⟩ },
    refl }
end

end

-- This sorry will be messy, but not impossible, to fill in. Need h.some_spec.2
lemma rational_open_subset.restriction_is_cts {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  continuous (rational_open_subset.restriction h) := Huber_ring.away.lift_continuous r1.T r1.s
  (localization.nonarchimedean r2)
  (Huber_ring.away.of_continuous r2.T r2.s
  (show ((localization.to_units (⟨r2.s, 1, by simp⟩ : powers r2.s))⁻¹ : units (localization r2)).inv =
    (of_id A (localization r2)).to_fun r2.s, from rfl) r2.Hopen) _ _ (begin
      refine power_bounded.subset _ (localization.power_bounded r2),
      intros x hx,
      rcases hx with ⟨y, hy, hz, ⟨t₁, ht₁, rfl⟩, rfl⟩,
      rw mem_singleton_iff at hy, rw hy, clear hy, clear y,
      let h' := h, -- need it later
      rcases h with ⟨a, ha, h₂⟩,
      rcases h₂ t₁ ht₁ with ⟨t₂, ht₂, N, hN⟩,
      show ↑(s_inv_aux r1 r2 _)⁻¹ * to_fun (localization r2) t₁ ∈
        localization.mk 1 ⟨r2.s, _⟩ • (of_id ↥A (localization r2)).to_fun '' r2.T,
      rw mem_smul_set,
      use (of_id ↥A (localization r2)).to_fun t₂,
      existsi _, swap,
        rw mem_image, use t₂, use ht₂,
      rw [←units.mul_left_inj (s_inv_aux r1 r2 h'), units.mul_inv_cancel_left],
      show to_fun (localization r2) t₁ = to_fun (localization r2) (r1.s) *
        (localization.mk 1 ⟨r2.s, _⟩ * to_fun (localization r2) t₂),
      rw [mul_comm, mul_assoc],
      rw ←units.mul_left_inj (localization.to_units (⟨r2.s, 1, by simp⟩ : powers r2.s)),
      rw ←mul_assoc,
      -- t1=s1*(1/s2 * t2) in r2
      have : ↑(localization.to_units (⟨r2.s, 1, by simp⟩ : powers r2.s)) *
        localization.mk (1 : A) (⟨r2.s, 1, by simp⟩ : powers r2.s) = 1,
      convert units.mul_inv _,
      rw [this, one_mul], clear this,
      show to_fun (localization r2) r2.s * _ = _,
      rw ←units.mul_left_inj (localization.to_units (⟨r2.s ^ N, N, rfl⟩ : powers r2.s)),
      show to_fun (localization r2) (r2.s ^ N) * _ = to_fun (localization r2) (r2.s ^ N) * _,
      have hrh : is_ring_hom (to_fun (localization r2)) := begin
        change is_ring_hom ((of_id ↥A (localization r2)).to_fun),
        apply_instance,
      end,
      rw ←@is_ring_hom.map_mul _ _ _ _ (to_fun (localization r2)) hrh,
      rw ←@is_ring_hom.map_mul _ _ _ _ (to_fun (localization r2)) hrh,
      rw ←@is_ring_hom.map_mul _ _ _ _ (to_fun (localization r2)) hrh,
      rw ←@is_ring_hom.map_mul _ _ _ _ (to_fun (localization r2)) hrh,
      congr' 1,
      rw [←mul_assoc _ t₂, hN],
      rw ←ha, ring,
    end)

-- Note: I don't think we ever use this.
noncomputable def insert_s (r : rational_open_data A) : rational_open_data A :=
{ s := r.s,
  T := insert r.s r.T,
  Tfin := set.fintype_insert r.s r.T, -- noncomputable!
  Hopen := submodule.is_open_of_open_submodule
    ⟨ideal.span (r.T), r.Hopen, ideal.span_mono $ set.subset_insert _ _⟩
}

-- not sure we ever use this
/-
noncomputable def inter_aux (r1 r2 : rational_open_data A) : rational_open_data A :=
{ s := r1.s * r2.s,
  T := r1.T * r2.T,
  Tfin := by apply_instance,
  Hopen := sorry /-
    need "product of open subgroups is open in a Huber ring" (because subgroup is open
    iff it contains I^N for some ideal of definition)
  -/
}
-/

end rational_open_data

lemma mk_mem_rational_open {s : A} {T : set A} {v : valuation A Γ} {hv : mk v ∈ Spa A} :
  (⟨mk v, hv⟩ : Spa A) ∈ rational_open s T ↔ (∀ t ∈ T, (v t ≤ v s)) ∧ (v s ≠ 0) :=
begin
  apply and_congr,
  { apply forall_congr,
    intro t,
    apply forall_congr,
    intro ht,
    apply out_mk },
  { apply (out_mk v).ne_zero }
end

definition rational_open_bInter (s : A) (T : set A) :
  rational_open s T = (⋂ t ∈ T, basic_open t s) ∩ {v | v s ≠ 0} :=
begin
  ext v,
  split; rintros ⟨h₁, h₂⟩; split; try { exact h₂ },
  { erw set.mem_bInter_iff,
    intros t ht,
    split,
    { exact h₁ t ht, },
    { exact h₂ } },
  { intros t ht,
    erw set.mem_bInter_iff at h₁,
    exact (h₁ t ht).1 }
end

lemma rational_open_add_s (s : A) (T : set A) :
  rational_open s T = rational_open s (insert s T) :=
begin
  ext v,
  split; rintros ⟨h₁, h₂⟩; split; try { exact h₂ }; intros t ht,
  { cases ht,
    { rw ht, exact le_refl _ },
    { exact h₁ t ht } },
  { apply h₁ t,
    exact mem_insert_of_mem _ ht }
end

lemma rational_open.is_open (s : A) (T : set A) [h : fintype T] :
  is_open (rational_open s T) :=
begin
  rw rational_open_bInter,
  apply is_open_inter,
  { apply is_open_bInter ⟨h⟩,
    intros,
    apply basic_open.is_open },
  { rw ← basic_open_eq s,
    apply basic_open.is_open },
end

lemma rational_open_inter.aux₁ {s₁ s₂ : A} {T₁ T₂ : set A}
  (h₁ : s₁ ∈ T₁) (h₂ : s₂ ∈ T₂) :
  rational_open s₁ T₁ ∩ rational_open s₂ T₂ ⊆
  rational_open (s₁ * s₂) ((*) <$> T₁ <*> T₂) :=
begin
  rintros v ⟨⟨hv₁, hs₁⟩, ⟨hv₂, hs₂⟩⟩,
  split,
  { rintros t ⟨_, ⟨t₁, ht₁, rfl⟩, ⟨t₂, ht₂, ht⟩⟩,
    subst ht,
    convert le_trans
      (linear_ordered_comm_monoid.mul_le_mul_right (hv₁ t₁ ht₁) _)
      (linear_ordered_comm_monoid.mul_le_mul_left  (hv₂ t₂ ht₂) _);
    apply valuation.map_mul },
  { rw with_zero.ne_zero_iff_exists at hs₁ hs₂,
    cases hs₁ with γ₁ hγ₁,
    cases hs₂ with γ₂ hγ₂,
    erw [valuation.map_mul, hγ₁, hγ₂],
    exact with_zero.coe_ne_zero },
end

lemma rational_open_inter.aux₂ {s₁ s₂ : A} {T₁ T₂ : set A}
  (h₁ : s₁ ∈ T₁) (h₂ : s₂ ∈ T₂) :
  rational_open (s₁ * s₂) ((*) <$> T₁ <*> T₂) ⊆
  rational_open s₁ T₁ ∩ rational_open s₂ T₂ :=
begin
  rintros v ⟨hv, hs⟩,
  have vmuls : v (s₁ * s₂) = v s₁ * v s₂ := valuation.map_mul _ _ _,
  have hs₁ : v s₁ ≠ 0 := λ H, by simpa [-coe_fn_coe_base, vmuls, H] using hs,
  have hs₂ : v s₂ ≠ 0 := λ H, by simpa [-coe_fn_coe_base, vmuls, H] using hs,
  split; split;
  try { assumption };
  intros t ht;
  rw with_zero.ne_zero_iff_exists at hs₁ hs₂,
  { suffices H : v t * v s₂ ≤ v s₁ * v s₂,
    { cases hs₂ with γ hγ,
      rw hγ at H,
      have := linear_ordered_comm_monoid.mul_le_mul_right H γ⁻¹,
      simp [mul_assoc, -coe_fn_coe_base] at this,
      erw [mul_one, mul_one] at this,
      exact this },
    { erw [← valuation.map_mul, ← valuation.map_mul],
      exact hv (t * s₂) ⟨_, ⟨t, ht, rfl⟩, ⟨s₂, h₂, rfl⟩⟩, } },
  { suffices H : v s₁ * v t ≤ v s₁ * v s₂,
    { cases hs₁ with γ hγ,
      rw hγ at H,
      have := linear_ordered_comm_monoid.mul_le_mul_left H γ⁻¹,
      erw [← mul_assoc, ← mul_assoc] at this,
      simp [-coe_fn_coe_base] at this,
      erw [one_mul, one_mul] at this,
      exact this },
    { erw [← valuation.map_mul, ← valuation.map_mul],
      exact hv _ ⟨_, ⟨s₁, h₁, rfl⟩, ⟨t, ht, rfl⟩⟩ } },
end

lemma rational_open_inter {s₁ s₂ : A} {T₁ T₂ : set A} (h₁ : s₁ ∈ T₁) (h₂ : s₂ ∈ T₂) :
  rational_open s₁ T₁ ∩ rational_open s₂ T₂ =
  rational_open (s₁ * s₂) ((*) <$> T₁ <*> T₂) :=
le_antisymm (rational_open_inter.aux₁ h₁ h₂) (rational_open_inter.aux₂ h₁ h₂)

@[simp] lemma rational_open_singleton {r s : A} :
rational_open s {r} = basic_open r s :=
begin
  apply le_antisymm; rintros v ⟨h₁, h₂⟩; split;
  intros; simp [*] at *,
end

@[simp] lemma basic_open_eq_univ : basic_open (1 : A) (1 : A) = univ :=
univ_subset_iff.1 $ λ v h, ⟨le_refl _,by erw valuation.map_one; exact one_ne_zero⟩

@[simp] lemma rational_open_eq_univ : rational_open (1 : A) {(1 : A)} = univ :=
by simp

def rational_basis (A : Huber_pair) : set (set (Spa A)) :=
{U : set (Spa A) | ∃ {s : A} {T : set A} {hfin : fintype T} {hopen : is_open (ideal.span T).carrier},
                   U = rational_open s T }

lemma rational_basis.is_basis.aux₁ (s₁ s₂ : A) (T₁ T₂ : set A) :
  (*) <$> T₁ <*> T₂ ⊆ (*) <$> (insert s₁ T₁) <*> (insert s₂ T₂) :=
begin
  rintros t ⟨_, ⟨t₁, ht₁, rfl⟩, ⟨t₂, ht₂, ht⟩⟩,
  exact ⟨_, ⟨t₁, mem_insert_of_mem _ ht₁, rfl⟩, ⟨t₂, mem_insert_of_mem _ ht₂, ht⟩⟩
end

-- Current status: proof is broken with 2 sorries.
-- KMB remarks that we don't need this result yet so he's commenting it out for now.
-- We might well need it though!

/-
lemma rational_basis.is_basis : topological_space.is_topological_basis (rational_basis A) :=
begin
split,
{ rintros U₁ ⟨s₁, T₁, hfin₁, hopen₁, H₁⟩ U₂ ⟨s₂, T₂, hfin₂, hopen₂, H₂⟩ v hv,
  use U₁ ∩ U₂,
  rw rational_open_add_s at H₁ H₂,
  split,
  { simp only [H₁, H₂, rational_open_inter, set.mem_insert_iff, true_or, eq_self_iff_true],
    resetI,
    refine ⟨_, _, infer_instance, _, rfl⟩,
    -- jmc: what follows is a sketch. We can fill the gaps once we know more about topological rings
    have foo := ideal.span_mono (rational_basis.is_basis.aux₁ s₁ s₂ T₁ T₂),
    suffices : is_open (ideal.span ((*) <$> T₁ <*> T₂)).carrier,
    { sorry /- use "foo" from two lines up -/ },
    { -- See the remarks in Wedhorn 7.30.(5).
      sorry } },
  { exact ⟨hv, subset.refl _⟩ } },
split,
{ apply le_antisymm,
  { exact subset_univ _ },
  { apply subset_sUnion_of_mem,
    refine ⟨(1 : A), {(1 : A)}, infer_instance, _, by simp⟩,
    rw ideal.span_singleton_one,
    exact is_open_univ, } },
{ apply le_antisymm,
  { delta Spa.topological_space,
    rw generate_from_le_iff_subset_is_open,
    rintros U ⟨r, s, H⟩,
    rw [H, ← rational_open_singleton],
    refine topological_space.generate_open.basic _ ⟨s, {r}, infer_instance, _, rfl⟩,
    sorry -- is this even true? I guess we shouldn't do the rw 2 lines up.
    -- Instead, we should use a smarter argument that I haven't cooked up yet.
     },
  { rw generate_from_le_iff_subset_is_open,
    rintros U ⟨s, T, hT, hT', H⟩,
    subst H,
    haveI := hT,
    exact rational_open.is_open s T,
  } }
end
-/

-- KMB remarks that we don't need the presheaf on the basic either
/-
namespace rational_open

def presheaf.aux (s : A) (T : set A) := localization.away s

instance (s : A) (T : set A) : comm_ring (presheaf.aux s T) :=
by delta presheaf.aux; apply_instance

-- Definition of A\left(\frac T s\right) as a topological ring
def presheaf.topology (rod : rational_open_data A) :
  topological_space (presheaf.aux rod.s rod.T) := sorry
/-
let As := presheaf.aux s T in
let S₁ : set As := localization.of '' A.RHuber.A₀ in
let T' : set As := localization.of '' T in
let S₂ : set As := (*) (((localization.to_units s)⁻¹ : units As) : As) '' T' in -- need to update mathlib
let S : set As := S₁ ∪ S₂ in
let D := ring.closure S in
let I := classical.some A.RHuber.A₀_is_ring_of_definition.2 in
adic_topology (I * D)
--  let As := presheaf.aux s T in sorry
 /-let D := ring.closure ((localize s) '' A.RHuber.A₀ ∪ (((λ x, x*s⁻¹) ∘ localize s) '' T)) in
 begin
   let nhd := λ n : ℕ, mul_ideal (pow_ideal ((localize s) '' A.Rplus) n) D,
  sorry
end-/
-/

def presheaf' (s : A) (T : set A) [Hfin : fintype T]
  (Hopen : _root_.is_open ((ideal.span T) : set A)) : Type* := sorry
-- ring_completion presheaf.aux s T

end rational_open
-/

def rational_open_data_subsets (U : set (Spa A)) (HU : is_open U) :=
{ r : rational_open_data A // r.rational_open ⊆ U}

local attribute [instance] topological_add_group.to_uniform_space

-- nearly there but doesn't compile :-( "deep recursion"
--def presheaf (U : set (Spa A)) (HU : is_open U) :=
--{f : Π (rd : rational_open_data_subsets U HU), ring_completion (rational_open_data.localization rd.1) //
--   ∀ (rd1 rd2 : rational_open_data_subsets U HU) (h : rd1.1 ≤ rd2.1),
--     rational_open_data.rational_open_subset.restriction h (f rd1) = (f rd2)} -- agrees on overlaps

end Spa

-- goal now to define the 𝓞_X on *rational subsets* and then to extend.

-- to define it on rational subsets it's just a ring completion.

-- remember that a rational open is not actually `rational_open s T` in full
-- generality -- we also need that T is finite and that T generates an open ideal in A.
-- The construction on p73/74 (note typo in first line of p74 -- ideal should be I.D)
-- gives A<T/s> (need completion) and A<T/s>^+ (need integral closure).

-- Once we have this, we see mid way through p75 that the definition of the presheaf
-- on V is proj lim of O_X(U) as U runs through rationals opens in V. This gets
-- the projective limit topology and then we have a presheaf (hopefully this is
-- straightforward) of complete topological rings (need proj lim of complete is complete)

-- We then need the valuations on the stalks (this is direct limit in cat of rings, forget
-- the topology). This will be fiddly but not impossible.

-- We then have an object in V^pre and I think then everything should follow.
