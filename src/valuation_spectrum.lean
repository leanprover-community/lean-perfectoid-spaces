import valuations 
import analysis.topology.topological_space
import data.finsupp
import for_mathlib.quotient_group

universes u u1 u2

open valuation 

definition Spv (R : Type u) [comm_ring R] := 
{ineq : R → R → Prop // ∃ (Γ : Type u) [linear_ordered_comm_group Γ],
  by exactI ∃ (v : valuation R Γ), ∀ r s : R, ineq r s ↔ v r ≤ v s}

namespace Spv 

#check multiplicative 

-- decidable equality on R to make the finsupp an add_comm_group?!
theorem value_group_universe (R : Type u1) [comm_ring R] [decidable_eq R] (Γ2 : Type u2) [linear_ordered_comm_group Γ2]
  (f2 : R → option Γ2) (Hf2 : is_valuation f2) : 
∃ (Γ1 : Type u1) [linear_ordered_comm_group Γ1], by exactI ∃ (f1 : R → option Γ1) (Hf1 : is_valuation f1),
  ∀ r s : R, f1 r ≤ f1 s ↔ f2 r ≤ f2 s := 
begin
  let FG : Type u1 := multiplicative (R →₀ ℤ), -- free group on R
  let φ₀ : R → Γ2 := λ r, option.get_or_else (f2 r) 1, 
  let φ : FG → Γ2 := λ f, finsupp.prod f (λ r n,(φ₀ r) ^ n),
  -- have H : comm_group (FG) := by apply_instance,
  have H0 : ∀ (a : R), φ₀ a ^ 0 = 1 := λ a,rfl,
  have Hprod:  ∀ (a : R) (b₁ b₂ : ℤ), φ₀ a ^ (b₁ + b₂) = φ₀ a ^ b₁ * φ₀ a ^ b₂ := 
    λ a b₁ b₂, gpow_add _ _ _,
  letI Hφ : is_group_hom φ :=
  { mul := λ a b,finsupp.prod_add_index H0 Hprod,
  },
  let N := is_group_hom.ker φ,
  let Γ1 := group.quotient_group N,
  existsi Γ1,
  let GΓ1 : group Γ1 := by apply_instance,
  let ψ : Γ1 → Γ2 := group.quotient.lift N φ (λ _,(is_group_hom.mem_ker φ).1),
  have Hψ : function.injective ψ := group.quotient.injective_lift N φ
  begin
    funext,apply propext,
    show x ∈ N ↔ _,
    exact is_group_hom.mem_ker φ,
  end,
  letI Γ1linord : linear_order Γ1 := 
  {

  },

  letI Γ1order : linear_ordered_comm_group Γ1 :=
  { mul_le_mul_left := sorry,
    mul_comm := sorry,
    ..GΓ1
  }
  -- let Γ1 be the quotient of FG by kernel of phi,
  -- write down injective group hom Γ1 -> Γ2
  -- deduce linear ordered comm group
  -- etc etc

end 
#print linear_order

definition quot.mk (R : Type u1) [comm_ring R] (Γ2 : Type u2) [linear_ordered_comm_group Γ2]
(f : R → option Γ2) (H : is_valuation f) : Spv R := sorry

-- and now a huge technical interlude, to define

-- Spv.mk (A : Type u) [comm_ring A] (Γ : Type v) -- note : v ≠ u 
-- [linear_ordered_comm_group Γ] (v : valuation A Γ) : Spv A := ...

-- quot.mk (f : A → option Γ) [ is_valuation f] : Spv A
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

-- Also need a variant of  Wedhorn 1.27 (ii) -/

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




variables {A : Type*} [comm_ring A]

definition basic_open (r s : A) : set (Spv A) := 
{v | v.val r s ∧ ¬ v.val s 0}

instance (A : Type*) [comm_ring A] : topological_space (Spv A) :=
topological_space.generate_from {U : set (Spv A) | ∃ r s : A, U = basic_open r s}

end Spv 
