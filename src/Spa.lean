import ring_theory.localization
import ring_theory.subring
import continuous_valuations
import Huber_pair

import for_mathlib.adic_topology
import for_mathlib.data.set.finite

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
    rw [valuation.map_one], }
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

-- Note: this lemma cannot be of any use to us because we're missing the
-- assumption that <T> is open.
-- jmc: the above remark is now out of date.
-- Current status: proof is broken with 2 sorries.
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


/-
The presheaf will be defined as the extension of a presheaf on the basis of rational opens.
So we will now first define a presheaf on this basis.
-/

namespace rational_open

def presheaf.aux (s : A) (T : set A) := localization.away s

instance (s : A) (T : set A) : comm_ring (presheaf.aux s T) :=
by delta presheaf.aux; apply_instance

/- This doesn't compile so I commented it out.

-- Definition of A\left(\frac T s\right) as a topological ring
def presheaf.topology (s : A) (T : set A) [Hfin : fintype T]
  (Hopen : _root_.is_open ((ideal.span T) : set A)) :
  topological_space (presheaf.aux s T) :=
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


def presheaf (s : A) (T : set A) [Hfin : fintype T]
  (Hopen : _root_.is_open ((ideal.span T) : set A)) :=
sorry -- ring_completion presheaf.aux s T
-/
end rational_open

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
