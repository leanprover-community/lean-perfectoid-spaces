import ring_theory.localization
import ring_theory.subring
import continuous_valuations
import Huber_pair

universes u₁ u₂ u₃

local attribute [instance, priority 0] classical.prop_decidable

open function Spv valuation

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

-- should only be applied with (HfinT : fintype T) and (Hopen: is_open (span T))
definition rational_open (s : A) (T : finset A) : set (Spa A) :=
{v | (∀ t ∈ T, (v t ≤ v s)) ∧ (v s ≠ 0)}

lemma mk_mem_rational_open {s : A} {T : finset A} {v : valuation A Γ} {hv : mk v ∈ Spa A} :
  (⟨mk v, hv⟩ : Spa A) ∈ rational_open s T ↔ (∀ t ∈ T, (v t ≤ v s)) ∧ (v s ≠ 0) :=
begin
  apply and_congr,
  { apply forall_congr,
    intro t,
    apply forall_congr,
    intro ht,
    apply out_mk, },
  { apply (out_mk v).ne_zero, },
end

definition rational_open_bInter (s : A) (T : finset A) :
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

lemma rational_open_add_s (s : A) (T : finset A) :
  rational_open s T = rational_open s (insert s T) :=
begin
  ext v,
  split; rintros ⟨h₁, h₂⟩; split; try { exact h₂ }; intros t ht,
  { rw finset.mem_insert at ht,
    cases ht,
    { rw ht, exact le_refl _ },
    { exact h₁ t ht } },
  { exact h₁ t (finset.mem_insert_of_mem ht), }
end

lemma rational_open.is_open (s : A) (T : finset A) :
  is_open (rational_open s T) :=
begin
  rw rational_open_bInter,
  apply is_open_inter,
  { apply is_open_bInter,
    { apply set.finite_mem_finset, },
    { intros,
      exact basic_open.is_open _ _ } },
  { rw ← basic_open_eq s,
    exact basic_open.is_open s s },
end

noncomputable def finset.monad : monad finset :=
  {pure := @finset.singleton, bind := λ α β, finset.bind }
local attribute [instance] finset.monad

lemma rational_open_inter.aux₁ {s₁ s₂ : A} {T₁ T₂ : finset A}
  (h₁ : s₁ ∈ T₁) (h₂ : s₂ ∈ T₂) :
  rational_open s₁ T₁ ∩ rational_open s₂ T₂ ⊆
  rational_open (s₁ * s₂) ((*) <$> T₁ <*> T₂) :=
begin
  rintros v ⟨⟨hv₁, hs₁⟩, ⟨hv₂, hs₂⟩⟩,
  have vmuls : v (s₁ * s₂) = v s₁ * v s₂ := valuation.map_mul _ _ _,
  split,
  { rintros t ht, --⟨_, ⟨t₁, ht₁, rfl⟩, t₂, ht₂, ht⟩,
    subst ht,
    have vmult : v (t₁ * t₂) = v t₁ * v t₂ := valuation.map_mul _ _ _,
    rw [vmuls, vmult],
    refine le_trans (linear_ordered_comm_monoid.mul_le_mul_left  (hv₂ _ ht₂) _)
                    (linear_ordered_comm_monoid.mul_le_mul_right (hv₁ _ ht₁) _ ) },
  { intro H,
    rw vmuls at H,
    cases H1 : v s₁ with γ₁, exact hs₁ H1,
    cases H2 : v s₂ with γ₂, exact hs₂ H2,
    rw [H1,H2] at H,
    change some (γ₁ * γ₂) = none at H,
    exact option.no_confusion H },
end

lemma rational_open_inter.aux₂ {s₁ s₂ : A} {T₁ T₂ : finset A}
  (h₁ : s₁ ∈ T₁) (h₂ : s₂ ∈ T₂) :
rational_open (s₁ * s₂) ((*) <$> T₁ <*> T₂) ⊆
rational_open s₁ T₁ ∩ rational_open s₂ T₂ :=
begin
  rintros v ⟨hv,hs⟩,
  have vmuls : v (s₁ * s₂) = v s₁ * v s₂ := valuation.map_mul _ _ _,
  have vs₁ne0 : v s₁ ≠ 0 := λ H, by simpa only [vmuls,H,zero_mul,ne.def,eq_self_iff_true,not_true] using hs,
  have vs₂ne0 : v s₂ ≠ 0 := λ H, by simpa only [vmuls,H,mul_zero,ne.def,eq_self_iff_true,not_true] using hs,
  split; split,
  { intros t ht,
    suffices H : v t * v s₂ ≤ v s₁ * v s₂,
    { cases H' : v s₂ with γ, exfalso; exact vs₂ne0 H',
      rw H' at H,
      have := linear_ordered_comm_monoid.mul_le_mul_right H (some (γ⁻¹)),
      conv at this { to_lhs, rw mul_assoc, congr, skip, change some (γ * γ⁻¹) },
      conv at this { to_rhs, rw mul_assoc, congr, skip, change some (γ * γ⁻¹) },
      simp only [mul_right_inv] at this,
      change v t * 1 ≤ v s₁ * 1 at this,
      rwa [mul_one,mul_one] at this },
    { rw ←vmuls,
      rw show v t * v s₂ = v (t * s₂), from (valuation.map_mul _ _ _).symm,
      refine hv (t * s₂) ⟨_,⟨_,ht,rfl⟩,_,h₂,rfl⟩ } },
  { exact vs₁ne0 },
  { intros t ht,
    suffices H : v s₁ * v t ≤ v s₁ * v s₂,
    { cases H' : v s₁ with γ, exfalso; exact vs₁ne0 H',
      rw H' at H,
      have := linear_ordered_comm_monoid.mul_le_mul_left H (some (γ⁻¹)),
      conv at this { to_lhs, rw ← mul_assoc, congr, change some (γ⁻¹ * γ) },
      conv at this { to_rhs, rw ← mul_assoc, congr, change some (γ⁻¹ * γ) },
      simp only [mul_left_inv] at this,
      change 1 * v t ≤ 1 * v s₂ at this,
      rwa [one_mul,one_mul] at this },
    { rw ←vmuls,
      rw show v s₁ * v t = v (s₁ * t), from (valuation.map_mul _ _ _).symm,
      refine hv _ ⟨_, ⟨s₁, h₁, rfl⟩, t, ht, rfl⟩ } },
  { exact vs₂ne0 }
end

lemma rational_open_inter {s₁ s₂ : A} {T₁ T₂ : set A} [fintype T₁] [fintype T₂] (h₁ : s₁ ∈ T₁) (h₂ : s₂ ∈ T₂) :
rational_open s₁ T₁ ∩ rational_open s₂ T₂ = rational_open (s₁ * s₂) ((*) <$> T₁ <*> T₂) :=
begin
  ext v, split; intro h,
  exact rational_open_inter.aux₁ h₁ h₂ h,
  exact rational_open_inter.aux₂ h₁ h₂ h
end

@[simp] lemma rational_open_singleton {r s : A} :
rational_open s {r} = basic_open r s :=
ext $ λ v,
{ mp  := λ h, ⟨h.left r (mem_singleton_iff.mpr rfl), h.right⟩,
  mpr := λ h, ⟨λ t ht,
          begin
            rw mem_singleton_iff at ht, subst ht,
            exact h.left
          end, h.right⟩ }

@[simp] lemma basic_open_eq_univ : basic_open (1 : A) (1 : A) = univ :=
begin
  apply le_antisymm,
  { exact subset_univ _ },
  { intros v h,
    split,
    exact le_refl _,
    have v1 : v 1 = 1 := valuation.map_one _,
    rw v1,
    intro h, exact option.no_confusion h },
end

@[simp] lemma rational_open_eq_univ : rational_open (1 : A) {(1 : A)} = univ :=
by simp

def rational_basis (A : Huber_pair) : set (set (Spa A)) :=
{U : set (Spa A) | ∃ {s : A} {T : set A} {h : fintype T}, U = rational_open s T }

attribute [instance] set.fintype_seq -- should move to mathlib

lemma rational_basis.is_basis : topological_space.is_topological_basis (rational_basis A) :=
begin
split,
{ rintros U₁ ⟨s₁, T₁, hfin₁, H₁⟩ U₂ ⟨s₂, T₂, hfin₂, H₂⟩ v hv,
  haveI := hfin₁,
  haveI := hfin₂,
  existsi U₁ ∩ U₂,
  rw rational_open_add_s at H₁ H₂,
  split,
  { simp [H₁, H₂,rational_open_inter,-set.fmap_eq_image,-set.seq_eq_set_seq],
    exact ⟨_,_,by apply_instance,rfl⟩ },
  { exact ⟨hv, subset.refl _⟩ } },
split,
{ apply le_antisymm,
  { exact subset_univ _ },
  apply subset_sUnion_of_mem,
  refine ⟨(1 : A), {(1 : A)}, by apply_instance, by simp⟩ },
{ apply le_antisymm,
  { unfold Spa.topological_space,
    rw generate_from_le_iff_subset_is_open,
    rintros U ⟨r, s, H⟩,
    rw [H,←rational_open_singleton],
    refine topological_space.generate_open.basic _ ⟨s, {r}, _, rfl⟩,
    exact set.fintype_singleton _ },
  { rw generate_from_le_iff_subset_is_open,
    rintros U ⟨s, T, hT, H⟩,
    subst H,
    haveI := hT,
    exact rational_open.is_open s T,
  } }
end

namespace rational_open
def presheaf.ring (s : A) := localization.away s

instance (s : A) : comm_ring (presheaf.ring s) :=
by dunfold presheaf.ring ; apply_instance

def localize (s : A) : A → presheaf.ring s := λ a, localization.of a 1

-- Definition of A\left(\frac T s\right) as a topological ring
def presheaf.top_ring (s : A) (T : set A) (HfinT : fintype T) :
   topological_space (presheaf.ring s) :=
 let As := presheaf.ring s in sorry
 /-let D := ring.closure ((localize s) '' A.RHuber.A₀ ∪ (((λ x, x*s⁻¹) ∘ localize s) '' T)) in
 begin
   let nhd := λ n : ℕ, mul_ideal (pow_ideal ((localize s) '' A.Rplus) n) D,
  sorry
end-/
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
