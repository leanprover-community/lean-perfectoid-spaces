import valuations 
import analysis.topology.topological_space
import data.finsupp
import group_theory.quotient_group

universes u₁ u₂ u₃

local attribute [instance] classical.prop_decidable

variables {R : Type u₁} [comm_ring R] [decidable_eq R]

structure Valuation (R : Type u₁) [comm_ring R] :=
(Γ   : Type u₁)
(grp : linear_ordered_comm_group Γ)
(val : @valuation R _ Γ grp)

namespace Valuation
open valuation

instance : has_coe_to_fun (Valuation R) :=
{ F := λ v, R → with_zero v.Γ, coe := λ v, v.val.val }

instance linear_ordered_value_group {v : Valuation R} : linear_ordered_comm_group v.Γ := v.grp

def of_valuation {Γ : Type u₂} [linear_ordered_comm_group Γ] (v : valuation R Γ) : Valuation R :=
{ Γ   := (minimal_value_group v).Γ,
  grp := minimal_value_group.linear_ordered_comm_group v,
  val := v.minimal_valuation }

section
variables (R)

instance : setoid (Valuation R) :=
{ r := λ v₁ v₂, ∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s,
  iseqv := begin
    split,
    { intros v r s, refl },
    split,
    { intros v₁ v₂ h r s, symmetry, exact h r s },
    { intros v₁ v₂ v₃ h₁ h₂ r s,
      exact iff.trans (h₁ r s) (h₂ r s) }
  end }

end

lemma ne_zero_of_equiv_ne_zero {Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁] {Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂]
{v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} {r : R} (heq : valuation.is_equiv v₁ v₂) (H : v₁ r ≠ 0) : v₂ r ≠ 0 :=
begin
  intro h,
  rw [eq_zero_iff_le_zero, ← heq r 0, ← eq_zero_iff_le_zero] at h,
  exact H h
end

end Valuation

section
variables (R)

definition Spv := {ineq : R → R → Prop // ∃ (v : Valuation R), ∀ r s : R, v r ≤ v s ↔ ineq r s}

end

namespace Spv
open valuation

definition mk (v : Valuation R) : Spv R := ⟨λ r s, v r ≤ v s, ⟨v, λ _ _, iff.rfl⟩⟩

definition mk' {Γ : Type u₂} [linear_ordered_comm_group Γ] (v : valuation R Γ) : Spv R := mk (Valuation.of_valuation v)

noncomputable definition out (v : Spv R) : Valuation R :=
subtype.cases_on v (λ ineq hv, classical.rec_on hv (λ v h, v))

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