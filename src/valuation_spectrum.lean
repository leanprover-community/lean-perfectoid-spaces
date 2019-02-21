import valuations
import topology.basic
import data.finsupp
import group_theory.quotient_group

universes u u₀ u₁ u₂ u₃

local attribute [instance] classical.prop_decidable

variables {R : Type u₀} [comm_ring R] [decidable_eq R]

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

definition Spv := {ineq : R → R → Prop // ∃ (v : Valuation R), ∀ r s : R, v r ≤ v s ↔ ineq r s}

variable {v : Spv R}

notation r `≤[`v`]` s := v.1 r s

end

namespace Spv
open valuation

definition mk (v : Valuation R) : Spv R := ⟨λ r s, v r ≤ v s, ⟨v, λ _ _, iff.rfl⟩⟩

definition mk' {Γ : Type u₂} [linear_ordered_comm_group Γ] (v : valuation R Γ) :
  Spv R :=
mk (Valuation.of_valuation v)

definition mk'' : large_Spv R → Spv R :=
quotient.lift mk $ λ (v₁ v₂ : Valuation R) h, subtype.ext.mpr $
begin
  ext r s,
  exact h r s,
end

section ineq

variables {v : Spv R}

-- @[refl] -- gives a weird error
lemma refl : reflexive v.1 := λ r,
begin
  cases v.2 with _ h,
  erw ← h at *,
  exact le_refl _,
end

-- @[trans]
lemma trans : transitive v.1 := λ r s t hrs hst,
begin
  cases v.2 with _ h,
  erw ← h at *,
  exact le_trans hrs hst,
end

@[simp] lemma zero_le (r : R) : 0 ≤[v] r :=
begin
  cases v.2 with w h,
  erw [← h, w.val.map_zero],
  simp,
end

@[simp] lemma add_le (r s : R) : ((r + s) ≤[v] r) ∨ ((r + s) ≤[v] s) :=
begin
  cases v.2 with w h,
  erw [← h, ← h],
  exact (w.val.map_add r s).imp id id,
end

@[simp] lemma mul_le_mul_left {r s : R} : (r ≤[v] s) → (∀ t, (t * r) ≤[v] (t * s)) :=
begin
  cases v.2 with w h,
  erw [← h],
  intros H t,
  erw [← h, w.val.map_mul, w.val.map_mul],
  exact linear_ordered_comm_monoid.mul_le_mul_left H _,
end

@[simp] lemma mul_le_mul_right {r s : R} : (r ≤[v] s) → (∀ t, (r * t) ≤[v] (s * t)) :=
begin
  cases v.2 with w h,
  erw [← h],
  intros H t,
  erw [← h, w.val.map_mul, w.val.map_mul],
  exact linear_ordered_comm_monoid.mul_le_mul_right H _,
end

@[simp] lemma not_one_le_zero : ¬ (1 ≤[v] 0) :=
begin
  cases v.2 with w h,
  erw [← h, w.val.map_one, w.val.map_zero],
  simp,
end

lemma mul_le_zero (r s : R) : (r * s ≤[v] 0) → (r ≤[v] 0) ∨ (s ≤[v] 0) :=
begin
  cases v.2 with w h,
  erw [← h, ← h, ← h, w.val.map_mul, w.val.map_zero],
  simpa using with_zero.eq_zero_or_eq_zero_of_mul_eq_zero _ _,
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
  cases v.2 with w h,
  erw [← h] at ⊢ H,
  convert val_add_supp_aux w.val (r + s) (-s) _,
  { simpa using (rfl : w r = w r) },
  { rw [w.val.map_neg],
    erw [w.val.map_zero] at H, }
end

def on_quot (v : Spv R) : Spv (supp v).quotient :=
{ val := @quotient.lift₂ _ _ _ ((supp v).quotient_rel) ((supp v).quotient_rel) v.1 $
    λ r₁ s₁ r₂ s₂ hr hs,
    begin
      have hr' : r₁ - r₂ ∈ supp v := hr,
      have hs' : s₁ - s₂ ∈ supp v := hs,
    end,
  property := _ }


noncomputable definition out (v : Spv R) : Valuation R :=
subtype.cases_on v (λ ineq hv, classical.some hv)

noncomputable definition lift {β : Type u₃}
(f : Valuation R → β) (H : ∀ v₁ v₂ : Valuation R, v₁ ≈ v₂ → f v₁ = f v₂) : Spv R → β :=
f ∘ out

lemma out_mk {v : Valuation R} : out (mk v) ≈ v := classical.some_spec (mk v).property

@[simp] lemma mk_out {v : Spv R} : mk (out v) = v :=
begin
  cases v with ineq hv,
  rw subtype.ext,
  ext,
  exact classical.some_spec hv _ _
end

lemma lift_mk {β : Type u₃} {f : Valuation R → β} {H : ∀ v₁ v₂ : Valuation R, v₁ ≈ v₂ → f v₁ = f v₂} (v : Valuation R) :
lift f H (mk v) = f v := H _ _ out_mk

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
  { exact Valuation.ne_zero_of_equiv_ne_zero out_mk h.right },
  { exact (out_mk r s).mpr h.left },
  { exact Valuation.ne_zero_of_equiv_ne_zero (setoid.symm out_mk) h.right }
end

instance : topological_space (Spv A) :=
topological_space.generate_from {U : set (Spv A) | ∃ r s : A, U = basic_open r s}

end Spv