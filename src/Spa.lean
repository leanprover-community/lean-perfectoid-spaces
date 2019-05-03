import ring_theory.localization
import ring_theory.subring
import continuous_valuations
import Huber_pair
import Huber_ring.localization

import for_mathlib.nonarchimedean.basic
import for_mathlib.data.set.finite
import for_mathlib.uniform_space.ring -- need completions of rings plus UMP
import for_mathlib.group -- some stupid lemma about units
import for_mathlib.sheaves.presheaf_of_topological_rings
import for_mathlib.topological_rings -- subring of a top ring

universes u₁ u₂ u₃

local attribute [instance, priority 0] classical.prop_decidable
local attribute [instance] set.pointwise_mul_comm_semiring

open set function Spv valuation

variables {Γ : Type*} [linear_ordered_comm_group Γ]

-- Wedhorn def 7.23.
definition spa (A : Huber_pair) : set (Spv A) :=
{v | v.is_continuous ∧ ∀ r ∈ A⁺, v r ≤ 1}

lemma mk_mem_spa {A : Huber_pair} {v : valuation A Γ} :
  mk v ∈ spa A ↔ v.is_continuous ∧ ∀ r ∈ A⁺, v r ≤ 1 :=
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

namespace spa

variable {A : Huber_pair}

instance : has_coe (spa A) (Spv A) := ⟨subtype.val⟩

definition basic_open (r s : A) : set (spa A) :=
{v | v r ≤ v s ∧ v s ≠ 0 }

lemma mk_mem_basic_open {r s : A} {v : valuation A Γ} {hv : mk v ∈ spa A} :
(⟨mk v, hv⟩ : spa A) ∈ basic_open r s ↔ v r ≤ v s ∧ v s ≠ 0 :=
begin
  apply and_congr,
  { apply out_mk, },
  { apply (out_mk v).ne_zero, },
end

-- instance (A : Huber_pair) : topological_space (spa A) :=
-- topological_space.generate_from {U : set (spa A) | ∃ r s : A, U = basic_open r s}

-- lemma basic_open.is_open (r s : A) : is_open (basic_open r s) :=
-- topological_space.generate_open.basic (basic_open r s) ⟨r, s, rfl⟩

-- lemma basic_open.compact (r s : A) : compact (basic_open r s) :=
-- sorry

lemma basic_open_eq (s : A) : basic_open s s = {v | v s ≠ 0} :=
set.ext $ λ v, ⟨λ h, h.right, λ h, ⟨le_refl _, h⟩⟩

-- should only be applied with (Hfin : fintype T) and (Hopen: is_open (span T))
definition rational_open (s : A) (T : set A) : set (spa A) :=
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

def rational_open (r : rational_open_data A) : set (spa A) :=
rational_open r.s r.T

def localization (r : rational_open_data A) := Huber_ring.away r.T r.s

instance ring_with_zero_nhd_of_localization (r : rational_open_data A) :
  ring_with_zero_nhd (localization r) :=
Huber_ring.away.ring_with_nhds  r.T r.s r.Hopen

instance (r : rational_open_data A) : comm_ring (localization r) :=
by unfold localization; apply_instance

instance (r : rational_open_data A) : topological_space (localization r) :=
ring_with_zero_nhd.topological_space _

instance (r : rational_open_data A) : topological_ring (localization r) :=
ring_with_zero_nhd.is_topological_ring _
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
to a *continuous* valuation on localization r1 which is bounded by 1 on some + subring;
one would now need to prove, at least, that every maximal ideal
is the support of a continuous valuation, which is Wedhorn 7.52(2). This is not
too bad -- but it is work that we have not yet done. However this is by no means the whole story;
we would also need that r1.T is power-bounded in localization.r2
and this looks much worse: it's Wedhorn 7.52(1). Everything is do-able, but it's just *long*.
Long as in "thousands more lines of code". We will need a good theory of primary and
secondary specialisation of valuations and so on and so on. None of this is there at
the time of writing, although I see no obstruction to putting it there, other than the
fact that it would take weeks of work.

We have to work with a weaker preorder then, because haven't made a good enough
API for continuous valuations. We basically work with the preorder r1 ≤ r2 iff
there's a continuous R-algebra map localization r2 → localization r1, i.e, we
define our way around the problem. We are fortunate in that we can prove
(in maths) that the projective limit over this preorder agrees with the projective
limit over the correct preorder.
-/

-- note: I don't think we ever use le_refl or le_trans. I only proved them to
-- validate the paper calculation I did which proves that the limit over these things
-- equals the limit over the things we'd rather be taking a limit over.
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

-- spa.rational_open_data.localization_map : the map between the uncompleted rings A(T1/s1)->A(T2/s2)
/-- The map A(T1/s1) -> A(T2/s2) coming from the inequality r1 ≤ r2 -/
noncomputable def localization_map {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  localization r1 → localization r2 :=
Huber_ring.away.lift r1.T r1.s
( show ((s_inv_aux r1 r2 h)⁻¹).inv = (of_id A (localization r2)).to_fun r1.s, from rfl)

instance {r1 r2 : rational_open_data A} (h : r1 ≤ r2) : is_ring_hom
(localization_map h) := by delta localization_map; apply_instance

lemma localization.nonarchimedean (r : rational_open_data A) :
  topological_add_group.nonarchimedean (localization r) :=
@is_subgroups_basis.nonarchimedean _ _ _ _ _ (Huber_ring.away.is_basis _ _ _)

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
  haveI := Huber_ring.away.is_basis r.T r.s r.Hopen,
  apply bounded.subset,
  work_on_goal 0 { apply add_group.subset_closure },
  show is_bounded (ring.closure (localization.power_bounded_data r)),
  intros U hU,
  rw is_subgroups_basis.nhds_zero at hU,
  cases hU with V hV,
  refine ⟨_, mem_nhds_sets (is_subgroups_basis.is_op _ V) _, _⟩,
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

end -- section

-- To prove continuity of the localisation map coming from r1 ≤ r2 I need to check
-- that the image of T/s in the r1 ring is power-bounded in the r2 ring. This is
-- this lemma.

lemma localization_map_is_cts_aux {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
is_power_bounded_subset
  ((s_inv_aux r1 r2 h)⁻¹.val • (λ (x : ↥A), to_fun (localization r2) x) '' r1.T) :=
begin
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
end

-- Continuity now follows from the universal property.
lemma localization_map_is_cts {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  continuous (localization_map h) := Huber_ring.away.lift_continuous r1.T r1.s
  (localization.nonarchimedean r2)
  (Huber_ring.away.of_continuous r2.T r2.s
  (show ((localization.to_units (⟨r2.s, 1, by simp⟩ : powers r2.s))⁻¹ : units (localization r2)).inv =
    (of_id A (localization r2)).to_fun r2.s, from rfl) r2.Hopen) _ _
    (localization_map_is_cts_aux h)

noncomputable def insert_s (r : rational_open_data A) : rational_open_data A :=
{ s := r.s,
  T := insert r.s r.T,
  Tfin := set.fintype_insert r.s r.T, -- noncomputable!
  Hopen := submodule.is_open_of_open_submodule
    ⟨ideal.span (r.T), r.Hopen, ideal.span_mono $ set.subset_insert _ _⟩
}


end rational_open_data -- namespace

lemma mk_mem_rational_open {s : A} {T : set A} {v : valuation A Γ} {hv : mk v ∈ spa A} :
  (⟨mk v, hv⟩ : spa A) ∈ rational_open s T ↔ (∀ t ∈ T, (v t ≤ v s)) ∧ (v s ≠ 0) :=
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

namespace rational_open_data

lemma insert_s_rational_open (r : rational_open_data A) :
(insert_s r).rational_open = r.rational_open := (rational_open_add_s r.s r.T).symm

lemma mem_insert_s (r : rational_open_data A) :
r.s ∈ (insert_s r).T := by {left, refl}

end rational_open_data

instance (A : Huber_pair) : topological_space (spa A) :=
topological_space.generate_from {U : set (spa A) | ∃ r : rational_open_data A, U = r.rational_open}

-- lemma rational_open.is_open (s : A) (T : set A) [h : fintype T] :
--   is_open (rational_open s T) :=
-- begin
--   rw rational_open_bInter,
--   apply is_open_inter,
--   { apply is_open_bInter ⟨h⟩,
--     intros,
--     apply basic_open.is_open },
--   { rw ← basic_open_eq s,
--     apply basic_open.is_open },
-- end

lemma rational_open_inter.aux₁ {s₁ s₂ : A} {T₁ T₂ : set A}
  (h₁ : s₁ ∈ T₁) (h₂ : s₂ ∈ T₂) :
  rational_open s₁ T₁ ∩ rational_open s₂ T₂ ⊆
  rational_open (s₁ * s₂) (T₁ * T₂) :=
begin
  rintros v ⟨⟨hv₁, hs₁⟩, ⟨hv₂, hs₂⟩⟩,
  split,
  { rintros t ⟨t₁, ht₁, t₂, ht₂, rfl⟩,
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
  rational_open (s₁ * s₂) (T₁ * T₂) ⊆
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
      exact hv (t * s₂) ⟨t, ht, s₂, h₂, rfl⟩, } },
  { suffices H : v s₁ * v t ≤ v s₁ * v s₂,
    { cases hs₁ with γ hγ,
      rw hγ at H,
      have := linear_ordered_comm_monoid.mul_le_mul_left H γ⁻¹,
      erw [← mul_assoc, ← mul_assoc] at this,
      simp [-coe_fn_coe_base] at this,
      erw [one_mul, one_mul] at this,
      exact this },
    { erw [← valuation.map_mul, ← valuation.map_mul],
      exact hv _ ⟨s₁, h₁, t, ht, rfl⟩ } },
end

lemma rational_open_inter {s₁ s₂ : A} {T₁ T₂ : set A} (h₁ : s₁ ∈ T₁) (h₂ : s₂ ∈ T₂) :
  rational_open s₁ T₁ ∩ rational_open s₂ T₂ =
  rational_open (s₁ * s₂) (T₁ * T₂) :=
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

def rational_basis (A : Huber_pair) : set (set (spa A)) :=
{U : set (spa A) | ∃ r : rational_open_data A, U = r.rational_open }

-- def rational_basis (A : Huber_pair) : set (set (spa A)) :=
-- {U : set (spa A) | ∃ {s : A} {T : set A} {hfin : fintype T} {hopen : is_open (↑(ideal.span T) : set A)},
--                    U = rational_open s T }

section
open algebra lattice

lemma rational_basis.is_basis.mul (T₁ T₂ : set A)
  (h₁ : is_open (↑(ideal.span T₁) : set A)) (h₂ : is_open (↑(ideal.span T₂) : set A)) :
  is_open (↑(ideal.span (T₁ * T₂)) : set A) :=
begin
  rcases Huber_ring.exists_pod_subset _ (mem_nhds_sets h₁ $ ideal.zero_mem $ ideal.span T₁)
    with ⟨A₀, _, _, _, ⟨_, emb, hf, I, fg, top⟩, hI⟩,
  dsimp only at hI,
  resetI,
  rw is_ideal_adic_iff at top,
  cases top.2 (algebra_map A ⁻¹' ↑(ideal.span T₂)) _ with n hn,
  { apply submodule.is_open_of_open_submodule,
    use ideal.map (of_id A₀ A) (I^(n+1)),
    refine ⟨is_open_ideal_map_open_embedding emb hf _ (top.1 (n+1)), _⟩,
    delta ideal.span,
    erw [pow_succ, ideal.map_mul, ← submodule.span_mul_span],
    apply submodule.mul_le_mul,
    { exact (ideal.span_le.mpr hI) },
    { rw ← image_subset_iff at hn,
      exact (ideal.span_le.mpr hn) } },
  { apply emb.continuous.tendsto,
    rw show algebra.to_fun A (0:A₀) = 0,
    { apply is_ring_hom.map_zero },
    exact (mem_nhds_sets h₂ $ ideal.zero_mem $ ideal.span T₂) }
end

end

namespace rational_open_data

noncomputable def inter_aux (r1 r2 : rational_open_data A) : rational_open_data A :=
{ s := r1.s * r2.s,
  T := r1.T * r2.T,
  Tfin := by apply_instance,
  Hopen := rational_basis.is_basis.mul r1.T r2.T r1.Hopen r2.Hopen
}

noncomputable def inter (r1 r2 : rational_open_data A) : rational_open_data A :=
inter_aux (rational_open_data.insert_s r1) (rational_open_data.insert_s r2)

lemma rational_open_data_inter (r1 r2 : rational_open_data A) :
(inter r1 r2).rational_open = r1.rational_open ∩ r2.rational_open :=
begin
  rw ←insert_s_rational_open r1,
  rw ←insert_s_rational_open r2,
  exact (rational_open_inter (mem_insert_s r1) (mem_insert_s r2)).symm
end

lemma rational_open_data_le_inter_left (r1 r2 : rational_open_data A) :
r1 ≤ (inter r1 r2) :=
begin
  use r2.s,
  split, refl,
  intros t1 ht1,
  use t1 * r2.s,
  existsi _,
    use 0,
  use t1,
  existsi _,
    use r2.s,
    existsi _, refl,
    exact mem_insert_s r2,
  right, assumption
end

lemma rational_open_data_le_inter_right (r1 r2 : rational_open_data A) :
r2 ≤ (inter r1 r2) :=
begin
  use r1.s,
  split, apply mul_comm,
  intros t2 ht2,
  use t2 * r1.s,
  existsi _,
    use 0,
  use r1.s,
  existsi _,
    use t2,
    existsi _, apply mul_comm,
    right, assumption,
  exact mem_insert_s r1,
end

lemma rational_open_data_symm (r1 r2 : rational_open_data A) :
  inter r1 r2 = inter r2 r1 :=
begin
  cases r1,
  cases r2,
    unfold inter inter_aux,
  congr' 1,
    unfold insert_s,
    dsimp, exact mul_comm _ _,
  unfold insert_s,
  dsimp,
  exact mul_comm _ _,
end

end rational_open_data

lemma rational_basis.is_basis.pow (T : set A) (hT : is_open (↑(ideal.span T) : set A)) (n : ℕ) :
  is_open (↑(ideal.span (T^n)) : set A) :=
begin
  induction n with n ih,
  { erw [pow_zero, ideal.span_singleton_one], exact is_open_univ },
  { rw pow_succ, exact rational_basis.is_basis.mul _ _ hT ih }
end

-- Rational opens form a basis of Spa(A). Current status: proof has some sorries.
-- Filling them may or may not be hard. We don't need it for the defition of an adic space.
/-
lemma exists_rational_open (X : set (spa A)) (hX : compact X)
  (s : A) (hs : ∀ v ∈ X, (v : Spv A) s ≠ 0) :
  ∃ (T : set A) (fin : fintype T) (hT : is_open (↑(ideal.span T) : set A)),
    X ⊆ rational_open s T :=
begin
  rcases Huber_ring.exists_pod_subset (univ : set A) (filter.univ_mem_sets)
    with ⟨A₀, _, _, _, ⟨_, emb, hf, I, fg, top⟩, hI⟩,
  rcases fg with ⟨T', hT'⟩,
  resetI,
  let T : set A := algebra_map A '' ↑T',
  haveI : fintype T := @set.fintype_image _ _ (by apply_instance) _ _ (finset_coe.fintype _),
  have hT : is_open (↑(ideal.span T) : set A) :=
  begin
    rw is_ideal_adic_iff at top,
    apply submodule.is_open_of_open_submodule,
    refine ⟨_, is_open_ideal_map_open_embedding emb hf I (pow_one I ▸ top.1 1), _⟩,
    change ideal.span _ = _ at hT',
    rw [← hT', ← ideal.span_image],
    exact le_refl _,
  end,
  have HT : is_topologically_nilpotent_subset T :=
  begin
    sorry
  end,
  have key : X ⊆ ⋃ (n ∈ (univ : set ℕ)), rational_open s (T^n) :=
  begin
    intros v hv,
    rw set.mem_Union,
    let U := (v : Spv A) ⁻¹' {γ | γ ≤ v s},
    cases HT U _ with n hn,
    refine ⟨n, _, _, _⟩,
    work_on_goal 1 { simp },
    work_on_goal 0 {
      split,
      { intros t ht,
        apply hn,
        exact ht },
      { exact hs v hv } },
    { apply mem_nhds_sets,
      have H := v.property.1,
      sorry,
      sorry }
  end,
  work_on_goal 0 {
    rcases compact_elim_finite_subcover_image hX _ key with ⟨c, csub, cfin, hc⟩,
    work_on_goal 1 { rintros _ ⟨n, rfl⟩, apply rational_open.is_open },
    refine ⟨T^(Sup c), by apply_instance, rational_basis.is_basis.pow T hT _, _⟩,
    refine set.subset.trans hc _,
    apply set.bUnion_subset,
    intros n hn v hv,
    refine ⟨_, hv.2⟩,
    intros t ht,
    sorry
  },
end
-/

variable (A)

def rational_open_data.univ : rational_open_data A :=
{ s := 1,
  T := {1},
  Tfin := by apply_instance,
  Hopen :=
  begin
    rw ideal.span_singleton_one,
    exact is_open_univ
  end }

lemma rational_open_data_univ :
  (rational_open_data.univ A).rational_open = univ :=
begin
  apply subset.antisymm (subset_univ _),
  intros v hv,
  split,
  { intros t ht,
    erw mem_singleton_iff at ht,
    subst ht,
    exact le_refl _ },
  { show v 1 ≠ 0,
    erw Spv.map_one,
    simp }
end

lemma rational_basis.is_basis : topological_space.is_topological_basis (rational_basis A) :=
begin
  refine ⟨_, _, rfl⟩,
  { rintros _ ⟨r₁, rfl⟩ _ ⟨r₂, rfl⟩ x hx,
    refine ⟨_, _, hx, subset.refl _⟩,
    { use rational_open_data.inter r₁ r₂,
      symmetry,
      apply rational_open_data.rational_open_data_inter } },
  { apply subset.antisymm (subset_univ _),
    apply subset_sUnion_of_mem,
    exact ⟨_, (rational_open_data_univ A).symm⟩ }
end

variable {A}

/-
-- Current status: proof is broken with 2 sorries.
-- We need this :-\
lemma rational_basis.is_basis : topological_space.is_topological_basis (rational_basis A) :=
begin
  split,
  { rintros U₁ ⟨s₁, T₁, hfin₁, hopen₁, H₁⟩ U₂ ⟨s₂, T₂, hfin₂, hopen₂, H₂⟩ v hv,
    refine ⟨U₁ ∩ U₂, _, hv, subset.refl _⟩,
    rw rational_open_add_s at H₁ H₂,
    simp only [H₁, H₂, rational_open_inter, set.mem_insert_iff, true_or, eq_self_iff_true],
    resetI,
    refine ⟨_, _, infer_instance, _, rfl⟩,
    apply rational_basis.is_basis.mul,
    all_goals {
      apply submodule.is_open_of_open_submodule,
      refine ⟨_, _, ideal.span_mono (subset_insert _ _)⟩,
      assumption } },
  split,
  { apply le_antisymm,
    { exact subset_univ _ },
    { apply subset_sUnion_of_mem,
      refine ⟨(1 : A), {(1 : A)}, infer_instance, _, by simp⟩,
      rw ideal.span_singleton_one,
      exact is_open_univ, } },
  { apply le_antisymm,
    { delta spa.topological_space,
      rw generate_from_le_iff_subset_is_open,
      rintros _ ⟨r, s, rfl⟩,
      rcases exists_rational_open _ (basic_open.compact r s) s (λ v hv, hv.2) with ⟨T, Tfin, hT, H⟩,
      resetI,
      have key : basic_open r s = rational_open s (insert r T) :=
      begin
        apply set.subset.antisymm,
        all_goals { intros v hv, refine ⟨_, hv.2⟩ },
        { intros t ht, rw mem_insert_iff at ht, rcases ht with rfl | ht,
          { exact hv.1 },
          { exact (H hv).1 t ht } },
        { exact hv.1 r (mem_insert _ _) }
      end,
      rw key,
      refine topological_space.generate_open.basic _ ⟨s, _, infer_instance, _, rfl⟩,
      apply submodule.is_open_of_open_submodule,
      exact ⟨_, hT, ideal.span_mono (subset_insert _ _)⟩ },
    { rw generate_from_le_iff_subset_is_open,
      rintros U ⟨s, T, hT, hT', H⟩,
      subst H,
      haveI := hT,
      exact rational_open.is_open s T,
    } }
end #check id
-/

section
open topological_space

def rational_open_data_subsets (U : opens (spa A)) :=
{ r : rational_open_data A // r.rational_open ⊆ U}
def rational_open_data_subsets.map {U V : opens (spa A)} (hUV : U ≤ V)
  (rd : rational_open_data_subsets U) :
  rational_open_data_subsets V :=
⟨rd.val, set.subset.trans rd.property hUV⟩

noncomputable def rational_open_data_subsets_inter {U :  opens (spa A)}
  (r1 r2 : rational_open_data_subsets U) :
rational_open_data_subsets U :=
⟨rational_open_data.inter r1.1 r2.1, begin
  rw rational_open_data.rational_open_data_inter,
  refine set.subset.trans (inter_subset_left r1.1.rational_open r2.1.rational_open) _,
  exact r1.2
end⟩

lemma rational_open_data_subsets_symm {U :  opens (spa A)}
  (r1 r2 : rational_open_data_subsets U) :
rational_open_data_subsets_inter r1 r2 = rational_open_data_subsets_inter r2 r1 :=
begin
  rw subtype.ext,
  exact rational_open_data.rational_open_data_symm r1.1 r2.1
end

instance (r : rational_open_data A) : uniform_space (rational_open_data.localization r) :=
topological_add_group.to_uniform_space _

instance (rd : rational_open_data A): uniform_add_group (rational_open_data.localization rd) :=
topological_add_group_is_uniform

def localization_map_is_uniform_continuous {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  uniform_continuous (rational_open_data.localization_map h) :=
uniform_continuous_of_continuous (rational_open_data.localization_map_is_cts h)

end -- section

-- r_o_d is short for "rational open data". KB needs to think more clearly
-- about namespaces etc.
/-- A<T/s>, the functions on D(T,s). A topological ring -/
def r_o_d_completion (r : rational_open_data A) :=
ring_completion (rational_open_data.localization r)

namespace r_o_d_completion
open topological_space

noncomputable instance (r : rational_open_data A) : comm_ring (r_o_d_completion r) :=
by dunfold r_o_d_completion; apply_instance

instance uniform_space (r : rational_open_data A) : uniform_space (r_o_d_completion r) :=
by dunfold r_o_d_completion; apply_instance

-- example (r : rational_open_data A) : topological_space (r_o_d_completion r) := by apply_instance

instance (r : rational_open_data A) : topological_ring (r_o_d_completion r)
:= by dunfold r_o_d_completion; apply_instance

noncomputable def restriction {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
r_o_d_completion r1 → r_o_d_completion r2 :=
ring_completion.map (rational_open_data.localization_map h)

instance restriction_is_ring_hom {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  is_ring_hom (restriction h) :=
by delta r_o_d_completion.restriction;
exact ring_completion.map_is_ring_hom _ _ (rational_open_data.localization_map_is_cts h)

lemma restriction_is_uniform_continuous {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
uniform_continuous (r_o_d_completion.restriction h) :=
ring_completion.map_uniform_continuous $ localization_map_is_uniform_continuous h

end r_o_d_completion -- namespace

open topological_space

/-- The underlying type of 𝒪_X(U), the structure presheaf on Spa(A) -/
def presheaf_value (U : opens (spa A)) :=
{f : Π (rd : rational_open_data_subsets U), r_o_d_completion rd.1 //
   ∀ (rd1 rd2 : rational_open_data_subsets U) (h : rd1.1 ≤ rd2.1),
     r_o_d_completion.restriction h (f rd1) = (f rd2)} -- agrees on overlaps

def presheaf_value_set (U : opens (spa A)) :=
{f : Π (rd : rational_open_data_subsets U), r_o_d_completion rd.1 |
   ∀ (rd1 rd2 : rational_open_data_subsets U) (h : rd1.1 ≤ rd2.1),
     r_o_d_completion.restriction h (f rd1) = (f rd2)}

-- We need to check it's a ring


instance presheaf_subring (U : opens (spa A)) : is_subring (presheaf_value_set U) :=
begin
refine {..},
  { -- zero_mem
    intros rd₁ rd₂ h,
    exact is_ring_hom.map_zero _ },
  { -- add_mem
    intros a b ha hb rd₁ rd₂ h,
    change r_o_d_completion.restriction h (a rd₁ + b rd₁) = a rd₂ + b rd₂,
    rw is_ring_hom.map_add (r_o_d_completion.restriction h),
    rw [ha _ _ h, hb _ _ h] },
  { -- neg_mem
    intros a ha rd₁ rd₂ h,
    change r_o_d_completion.restriction h (-(a rd₁)) = -(a rd₂),
    rw is_ring_hom.map_neg (r_o_d_completion.restriction h),
    rw ha _ _ h },
  { -- one_mem
    intros rd₁ rd₂ h,
    exact is_ring_hom.map_one _ },
  { -- mul_mem
    intros a b ha hb rd₁ rd₂ h,
    change r_o_d_completion.restriction h (a rd₁ * b rd₁) = a rd₂ * b rd₂,
    rw is_ring_hom.map_mul (r_o_d_completion.restriction h),
    rw [ha _ _ h, hb _ _ h] }
end

noncomputable instance presheaf_comm_ring (U : opens (spa A)) : comm_ring (presheaf_value U) :=
begin
  apply @subset.comm_ring _ pi.comm_ring _ _, apply_instance,
  exact spa.presheaf_subring U
end

instance presheaf_top_space (U : opens (spa A)) : topological_space (presheaf_value U) :=
by unfold presheaf_value; apply_instance

example (U : opens (spa A)) :
  topological_ring (Π (rd : rational_open_data_subsets U), r_o_d_completion (rd.1)) :=
by apply_instance

-- tactic mode because I can't get Lean to behave. Note: switching to tactic
-- mode indicated the problem was that Lean was not finding the two instances I flag
-- with haveI and letI; probably now I know this one could try to go back into term mode.
instance presheaf_top_ring (U : opens (spa A)) : topological_ring (presheaf_value U) :=
begin
  haveI := spa.presheaf_subring U,
  letI : topological_ring (Π (rd : rational_open_data_subsets U), r_o_d_completion (rd.1)) :=
    by apply_instance,
  apply topological_subring (presheaf_value_set U),
end

instance (U : opens (spa A)) (r : rational_open_data_subsets U) :
  is_ring_hom (λ (f : presheaf_value U), f.val r) :=
{ map_one := rfl,
  map_mul := λ _ _, rfl,
  map_add := λ _ _, rfl }

def presheaf_map {U V : opens (spa A)} (hUV : U ≤ V) :
  presheaf_value V → presheaf_value U :=
λ f, ⟨λ rd, f.val ⟨rd.val, set.subset.trans rd.2 hUV⟩,
begin
  intros,
  let X := f.2 (rational_open_data_subsets.map hUV rd1)
    (rational_open_data_subsets.map hUV rd2) h,
  exact X,
end⟩

lemma presheaf_map_id (U : opens (spa A)) :
  presheaf_map (le_refl U) = id :=
by { delta presheaf_map, tidy }

lemma presheaf_map_comp {U V W : opens (spa A)} (hUV : U ≤ V) (hVW : V ≤ W) :
  presheaf_map hUV ∘ presheaf_map hVW = presheaf_map (le_trans hUV hVW) :=
by { delta presheaf_map, tidy }

instance presheaf_map_is_ring_hom {U V : opens (spa A)} (hUV : U ≤ V) :
is_ring_hom (presheaf_map hUV) :=
{ map_one := rfl,
  map_mul := λ _ _, rfl,
  map_add := λ _ _, rfl }

def presheaf_map_cts {U V : opens (spa A)} (hUV : U ≤ V) :
  continuous (presheaf_map hUV) :=
continuous_subtype_mk _ (continuous_pi (λ i, (continuous.comp (continuous_subtype_val) (continuous_apply _))))

variable (A)
noncomputable def presheaf_of_topological_rings : presheaf_of_topological_rings (spa A) :=
{ F := presheaf_value,
  res := λ U V, presheaf_map,
  Hid := presheaf_map_id,
  Hcomp := λ U V W, presheaf_map_comp,
  Fring := spa.presheaf_comm_ring,
  res_is_ring_hom := λ U V, spa.presheaf_map_is_ring_hom,
  Ftop := spa.presheaf_top_space,
  Ftop_ring := spa.presheaf_top_ring,
  res_continuous := λ U V, presheaf_map_cts
}


end spa -- namespace I think

-- old notes

-- remember that a rational open is not actually `rational_open s T` in full
-- generality -- we also need that T is finite and that T generates an open ideal in A.
-- The construction on p73/74 (note typo in first line of p74 -- ideal should be I.D)
-- gives A<T/s> (need completion) and A<T/s>^+ (need integral closure).

-- KB idle comment: I guess we never make A<T/s> a Huber pair if A is a Huber pair?
-- We would need integral closure for this and I don't think we have it in mathlib.

-- We see mid way through p75 that the definition of the presheaf
-- on V is proj lim of O_X(U) as U runs through rationals opens in V. This gets
-- the projective limit topology and then we have a presheaf (hopefully this is
-- straightforward) of complete topological rings (need proj lim of complete is complete)
