import valuations 
import analysis.topology.topological_space
import data.finsupp
import group_theory.quotient_group

universes u₁ u₂ u₃

open valuation

variables (R : Type u₁) [comm_ring R] [decidable_eq R]

structure Valuation (R : Type u₁) [comm_ring R] :=
(Γ   : Type u₁)
(grp : linear_ordered_comm_group Γ)
(val : @valuation R _ Γ grp)

namespace Valuation

instance : has_coe_to_fun (Valuation R) :=
{ F := λ v, R → with_zero v.Γ, coe := λ v, v.val.val }

instance linear_ordered_value_group {v : Valuation R} : linear_ordered_comm_group v.Γ := v.grp

end Valuation

instance Spv.setoid : setoid (Valuation R) :=
{ r := λ v₁ v₂, ∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s,
  iseqv := begin
    split,
    { intros v r s, refl },
    split,
    { intros v₁ v₂ h r s, symmetry, exact h r s },
    { intros v₁ v₂ v₃ h₁ h₂ r s,
      exact iff.trans (h₁ r s) (h₂ r s) }
  end }

definition Spv := quotient (Spv.setoid R)
-- {ineq : R → R → Prop // ∃ {Γ : Type u₁} [linear_ordered_comm_group Γ],
--   by exactI ∃ (v : valuation R Γ), ∀ r s : R, v r ≤ v s ↔ ineq r s}

namespace Spv

variables {R} {Γ : Type u₂} [linear_ordered_comm_group Γ]

definition mk (v : valuation R Γ) : Spv R :=
quotient.mk
{ Γ  := (minimal_value_group v).Γ,
  grp := minimal_value_group.linear_ordered_comm_group v,
  val := v.minimal_valuation }

definition lift {β : Type u₃} (f : Valuation R → β) (H : ∀ v₁ v₂ : Valuation R, v₁ ≈ v₂ → f v₁ = f v₂) :
Spv R → β := quotient.lift f H

definition ind {f : Spv R → Prop} (H : ∀ v, f ⟦v⟧) : ∀ v : Spv R, f v := quotient.ind H

end Spv 

-- TODO:

-- quot.lift takes a function defined on valuation functions and produces a function defined on Spv
-- quot.ind as well
--or equivalently quot.exists_rep
-- exists_rep {α : Sort u} {r : α → α → Prop} (q : quot r) : ∃ a : α, (quot.mk r a) = q :=
-- that is, for every element of Spv there is a valuation function that quot.mk's to it
-- Note it's not actually a function producing valuation functions, it's an exists
-- if you prove analogues of those theorems for your type, then you have constructed the
--  quotient up to isomorphism
-- This all has a category theoretic interpretation as a coequalizer, and all constructions
--  are natural in that category
-- As opposed to, say, quot.out, which picks an element from an equivalence class
-- Although in your case if I understand correctly you also have a canonical way to define quot.out
--  satisfying some other universal property to do with the ordered group

-- **also need to check that continuity is well-defined on Spv R**
-- continuity of an inequality is defined using the minimal Gamma
-- need value_group_f v₁ = set.univ

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
Spv.lift (λ v : Valuation A, v r ≤ v s ∧ ¬ v s ≤ v 0) (λ v₁ v₂ h,
begin
  ext,
  dsimp [valuation.is_equiv] at h,
  split; intro; split; rw h at *;
  try {exact a.left}; try {exact a.right},
  rw h at *, exact a.right
end)

instance : topological_space (Spv A) :=
topological_space.generate_from {U : set (Spv A) | ∃ r s : A, U = basic_open r s}

end Spv 