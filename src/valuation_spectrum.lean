import topology.basic
import group_theory.quotient_group
import valuation.canonical

universes u u₀ u₁ u₂ u₃

--local attribute [instance, priority 0] classical.prop_decidable

variables {R : Type u₀} [comm_ring R] --[decidable_eq R]
variables {Γ : Type u} [linear_ordered_comm_group Γ]
variables {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]
/- this structure is evil
structure Valuation (R : Type u₀) [comm_ring R] :=
(Γ   : Type u)
(grp : linear_ordered_comm_group Γ)
(val : @valuation R _ Γ grp)

namespace Valuation
open valuation

instance : has_coe_to_fun (Valuation R) :=
{ F := λ v, R → with_zero v.Γ, coe := λ v, v.val.val }

instance linear_ordered_value_group {v : Valuation R} : linear_ordered_comm_group v.Γ := v.grp

def of_valuation {Γ : Type u} [linear_ordered_comm_group Γ] (v : valuation R Γ) : Valuation R :=
{ Γ   := Γ,
  grp := by apply_instance,
  val := v }

section
variables (R)

instance equiv : setoid (Valuation R) :=
{ r := λ v₁ v₂, v₁.val.is_equiv v₂.val,
  iseqv :=
  ⟨λ _,     valuation.is_equiv.refl,
   λ _ _,   valuation.is_equiv.symm,
   λ _ _ _, valuation.is_equiv.trans ⟩}

end

@[simp] lemma equiv_eq {v₁ v₂ : Valuation R} : (v₁ ≈ v₂) = (v₁.val.is_equiv v₂.val) := rfl

-- -- If we need this, it should go to the valuations.lean file
-- lemma ne_zero_of_equiv_ne_zero {Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁] {Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂]
-- {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} {r : R} (heq : valuation.is_equiv v₁ v₂) (H : v₁ r ≠ 0) : v₂ r ≠ 0 :=
-- begin
--   intro h,
--   rw [eq_zero_iff_le_zero, ← heq r 0, ← eq_zero_iff_le_zero] at h,
--   exact H h
-- end

end Valuation

section
variables (R)

definition large_Spv := quotient (Valuation.equiv R)
-/

definition Spv (R : Type u₀) [comm_ring R] :=
{ineq : R → R → Prop // ∃ {Γ₀ : Type u₀} [linear_ordered_comm_group Γ₀],
 by exactI ∃ (v : valuation R Γ₀), ∀ r s : R, v r ≤ v s ↔ ineq r s}

variable {v : Spv R}

local notation r `≤[`v`]` s := v.1 r s

namespace Spv
open valuation

definition mk (v : valuation R Γ) : Spv R :=
⟨λ r s, v r ≤ v s,
  ⟨value_group v, by apply_instance, canonical_valuation v, canonical_valuation_is_equiv v⟩⟩

@[simp] lemma mk_val (v : valuation R Γ) : (mk v).val = λ r s, v r ≤ v s := rfl

definition out_Γ (v : Spv R) : Type u₀ := classical.some v.2

noncomputable instance (v : Spv R) : linear_ordered_comm_group (out_Γ v) :=
classical.some $ classical.some_spec v.2

noncomputable definition out (v : Spv R) : valuation R (out_Γ v) :=
classical.some $ classical.some_spec $ classical.some_spec v.2

@[simp] lemma mk_out {v : Spv R} : mk (out v) = v :=
begin
  rcases v with ⟨ineq, hv⟩,
  rw subtype.ext,
  ext,
  exact classical.some_spec (classical.some_spec (classical.some_spec hv)) _ _,
end

lemma out_mk (v : valuation R Γ) : (out (mk v)).is_equiv v :=
classical.some_spec (classical.some_spec (classical.some_spec (mk v).2))

noncomputable def lift {X}
  (f : Π ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group Γ₀], valuation R Γ₀ → X) (v : Spv R) : X :=
f (out v)

theorem lift_eq {X}
  (f₀ : Π ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group Γ₀], valuation R Γ₀ → X)
  (f : Π ⦃Γ : Type u⦄ [linear_ordered_comm_group Γ], valuation R Γ → X)
  (v : valuation R Γ)
  (h : ∀ ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group Γ₀] (v₀ : valuation R Γ₀), v₀.is_equiv v → f₀ v₀ = f v) :
  lift f₀ (mk v) = f v :=
h _ (out_mk v)

lemma exists_rep (v : Spv R) :
  ∃ {Γ₀ : Type u₀} [linear_ordered_comm_group Γ₀], by exactI ∃ (v₀ : valuation R Γ₀),
  mk v₀ = v :=
⟨out_Γ v, infer_instance, out v, mk_out⟩

lemma sound {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} (h : v₁.is_equiv v₂) : mk v₁ = mk v₂ :=
begin
  apply subtype.val_injective,
  ext r s,
  apply h,
end

/-
definition mk' {Γ : Type u₂} [linear_ordered_comm_group Γ] (v : valuation R Γ) :
  Spv R :=
mk (Valuation.of_valuation v)

definition mk'' : large_Spv R → Spv R :=
quotient.lift mk $ λ (v₁ v₂ : Valuation R) h, subtype.ext.mpr $
begin
  ext r s,
  exact h r s,
end
-/

-- jmc: I now think the following section is basically useless.
-- Mario clearly said that computable out is not really worth anything.
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Perfectoid.20spaces/near/160027955
section ineq

-- @[refl] -- gives a weird error
lemma refl : ∀ r : R, (v.1) r r := λ r,
begin
  rcases v.2 with ⟨Γ, hΓ, v0, h⟩,
  rw ←h,
  exactI le_refl (v0 r),
end

-- @[trans]
lemma trans : transitive v.1 := λ r s t hrs hst,
begin
  rcases v.2 with ⟨Γ, hΓ, v0, h⟩,
  rw ←h at hrs hst ⊢,
  exactI le_trans hrs hst,
end

@[simp] lemma zero_le (r : R) : 0 ≤[v] r :=
begin
  rcases v.2 with ⟨Γ, hΓ, v0, h⟩,
  letI := hΓ,
  rw [←h, v0.map_zero],
  simp,
end

@[simp] lemma add_le (r s : R) : ((r + s) ≤[v] r) ∨ ((r + s) ≤[v] s) :=
begin
  rcases v.2 with ⟨Γ, hΓ, v0, h⟩,
  letI := hΓ,
  rw [←h, ←h],
  exact (v0.map_add r s).imp id id,
end

@[simp] lemma mul_le_mul_left {r s : R} : (r ≤[v] s) → (∀ t, (t * r) ≤[v] (t * s)) :=
begin
  rcases v.2 with ⟨Γ, hΓ, v0, h⟩,
  letI := hΓ,
  rw ←h,
  intros H t,
  rw [←h, v0.map_mul, v0.map_mul],
  exact linear_ordered_comm_monoid.mul_le_mul_left H _,
end

@[simp] lemma mul_le_mul_right {r s : R} : (r ≤[v] s) → (∀ t, (r * t) ≤[v] (s * t)) :=
begin
  rcases v.2 with ⟨Γ, hΓ, v0, h⟩,
  letI := hΓ,
  rw ←h,
  intros H t,
  rw [←h, v0.map_mul, v0.map_mul],
  exact linear_ordered_comm_monoid.mul_le_mul_right H _,
end

@[simp] lemma not_one_le_zero : ¬ (1 ≤[v] 0) :=
begin
  rcases v.2 with ⟨Γ, hΓ, v0, h⟩,
  letI := hΓ,
  rw [←h, v0.map_one, v0.map_zero],
  simp,
end

lemma mul_le_zero (r s : R) : (r * s ≤[v] 0) → (r ≤[v] 0) ∨ (s ≤[v] 0) :=
begin
  rcases v.2 with ⟨Γ, hΓ, v0, h⟩,
  letI := hΓ,
  rw [←h, ←h, ←h, ←eq_zero_iff_le_zero, ←eq_zero_iff_le_zero,
    ←eq_zero_iff_le_zero, v0.map_mul],
    exact with_zero.eq_zero_or_eq_zero_of_mul_eq_zero _ _,
end

end ineq

def supp (v : Spv R) : ideal R :=
{ carrier := {r | r ≤[v] 0},
  zero := refl _,
  add := λ r s hr hs, by cases (add_le r s) with h h; refine trans h _; assumption,
  smul := λ t r h, by simpa using mul_le_mul_left h t }

instance supp_is_prime (v : Spv R) : (supp v).is_prime :=
begin
  split,
  { rw ideal.ne_top_iff_one,
    exact not_one_le_zero, },
  { intros r s,
    exact mul_le_zero _ _, }
end

@[simp] lemma le_add_right {v : Spv R} (r s : R) (H : s ≤[v] 0) : r ≤[v] r + s :=
begin
  rcases v.2 with ⟨Γ, hΓ, v0, h⟩,
  letI := hΓ,
  rw ←h at ⊢ H,
  convert val_add_supp_aux v0 (r + s) (-s) _,
  { simp},
  { rwa [v0.map_neg, eq_zero_iff_le_zero] }
end

/- Here is a roadmap for a computable quotient API for Spv.
Let me first say that I have only
now realised that this needs some work (I think Johan realised a while ago)

Throughout, v : Spv(R) [as opposed to v : valuation R Γ -- should we switch
notation for these equiv classes? Everything is called v :- / ]
[rofl I can't remove the space in the smiley :- / because it ends the comment]

*) Spv.sound is easy I think: if v1 and v2 are equiv then mk v0 = mk v1
almost by definition.

*) But Spv.out is still a journey (and quite a fun one).

1) Johan has proved supp(v) is prime and le_add_right above. So now given
v : Spv(R) we could, I believe, define v_quot : Spv(R/supp(v)); the inequality
on R/supp(v) can be defined using quotient.lift_on'₂ or whatever it's called,
and the existence of the valuation can be proved computably using v.on_quot.

2) Similarly given v: Spv(R) we can define v_frac : Spv(Frac(R/supp(v)))
in the same sort of way, using on_frac.

3) Now we define value_group v = Gamma_v to be the units in Frac(R/supp(v)) modulo the
units satisfying ineq x 1 and ineq 1 x, and prove that this is a linearly
ordered comm group.

4) And the canonical map from R to this can be proved to be a valuation.
That's Spv.out : Pi (v : Spv(R)), valuation R (value_group v)

*) I forgot what this is called, but we will need that
if v0 : valuation R Γ then is_equiv v0 (Spv.out (mk v0)).

We also need to prove mk (out v) = v I guess. These are related.

*) I think the type of Spv.lift should be

∀ (f : Σ Γ, valuation R Γ → X),
  (∀ v1 v2 : Σ Γ, valuation R Γ, is_equiv v1.2 v2.2)
  → Spv R → X

We can define Spv.lift f h v to be f(⟨value_group v, out v⟩).

Then we need to prove for v : valuation R Γ we have lift f h (mk v) = f ⟨Γ,v⟩
and the proof comes from h.

-/


#exit


def on_quot (v : Spv R) : Spv (supp v).quotient :=
{ val := @quotient.lift₂ _ _ _ ((supp v).quotient_rel) ((supp v).quotient_rel) v.1 $
    λ r₁ s₁ r₂ s₂ hr hs,
    begin
      have hr' : r₁ - r₂ ∈ supp v := hr,
      have hs' : s₁ - s₂ ∈ supp v := hs,
      sorry -- KB added this because he's not sure what's going on but wanted to get rid of the error
    end,
  property := sorry} -- ditto




lemma exists_rep (v : Spv R) : ∃ v' : Valuation R, mk v' = v := ⟨out v, mk_out⟩

lemma ind {f : Spv R → Prop} (H : ∀ v, f (mk v)) : ∀ v, f v :=
λ v, by simpa using H (out v)

lemma sound {v₁ v₂ : Valuation R} (heq : v₁ ≈ v₂) : mk v₁ = mk v₂ :=
begin
  rw subtype.ext,
  funext,
  ext,
  exact heq _ _
end

noncomputable instance : has_coe (Spv R) (Valuation R) := ⟨out⟩

end Spv

-- TODO:
-- Also might need a variant of  Wedhorn 1.27 (ii) -/

/-
theorem equiv_value_group_map (R : Type) [comm_ring R] (v w : valuations R) (H : v ≈ w) :
∃ φ : value_group v.f → value_group w.f, is_group_hom φ ∧ function.bijective φ :=
begin
  existsi _,tactic.swap,
  { intro g,
    cases g with g Hg,
    unfold value_group at Hg,
    unfold group.closure at Hg,
    dsimp at Hg,
    induction Hg,
  },
  {sorry

  }
end
-/

namespace Spv

variables {A : Type u₁} [comm_ring A] [decidable_eq A]

definition basic_open (r s : A) : set (Spv A) :=
{v | v r ≤ v s ∧ v s ≠ 0}

lemma mk_mem_basic_open {r s : A} (v : Valuation A) : mk v ∈ basic_open r s ↔ v r ≤ v s ∧ v s ≠ 0 :=
begin
  split; intro h; split,
  { exact (out_mk r s).mp h.left },
  { sorry},
--  { exact Valuation.ne_zero_of_equiv_ne_zero out_mk h.right },
  { exact (out_mk r s).mpr h.left },
  { sorry}
--  { exact Valuation.ne_zero_of_equiv_ne_zero (setoid.symm out_mk) h.right }
end

instance : topological_space (Spv A) :=
topological_space.generate_from {U : set (Spv A) | ∃ r s : A, U = basic_open r s}

end Spv
