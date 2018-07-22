import valuations 
import analysis.topology.topological_space
import data.finsupp
import for_mathlib.quotient_group
import valuation_universe 

universes u u1 u2

open valuation 

definition Spv (R : Type u) [comm_ring R] := 
{ineq : R → R → Prop // ∃ (Γ : Type u) [linear_ordered_comm_group Γ],
  by exactI ∃ (v : valuation R Γ), ∀ r s : R, ineq r s ↔ v r ≤ v s}

namespace Spv 

set_option class.instance_max_depth 100

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
  let ψ : Γ1 → Γ2 := group.quotient.lift N φ (λ _,(is_group_hom.mem_ker φ).1),
  have Hψ : function.injective ψ := group.quotient.injective_lift N φ
    begin
    funext,apply propext,
    show x ∈ N ↔ _,
    exact is_group_hom.mem_ker φ,
    end,
  letI Γ1linord : linear_order Γ1 := 
  { le := λ g h,ψ g ≤ ψ h,
    le_refl := λ _,le_refl _,
    le_trans := λ _ _ _ hab hbc,le_trans hab hbc,
    le_antisymm := λ g h Hgh Hhg,Hψ $ le_antisymm Hgh Hhg,
    le_total := λ g h, le_total _ _
  },
  letI Γ1order : linear_ordered_comm_group Γ1 :=
  { mul_le_mul_left := λ a b H c,
      begin 
      show ψ (c * a) ≤ ψ (c * b),
        rw is_group_hom.mul ψ c b,
        rw is_group_hom.mul ψ c a,
        exact linear_ordered_comm_group.mul_le_mul_left H _
      end
  },
  existsi Γ1,
  existsi Γ1order,
  let f1 : R → option Γ1 := (λ r, 
--    match (f2 r) with
--    | none := none
--    | some _ := some (group.quotient.mk N (finsupp.single r (1 : ℤ)))
--    end : R → option Γ1),
  option.rec_on (f2 r) (none : option Γ1) 
    (λ (r' : Γ2), (group.quotient.mk N (finsupp.single r (1 : ℤ)) : option Γ1))),
  existsi f1,
  -- equation lemma :-)
  have H12 : ∀ r : R, option.map ψ (f1 r) = f2 r,
  { intro r,
    dsimp [f1],
    destruct (f2 r),
    { intro Hnone,
      rw Hnone,
      refl},
    intro val,
    intro Hval,
    rw Hval,
    show some (ψ ((group.quotient.mk N (finsupp.single r 1)))) = some val,
    congr' 1,
    show group.quotient.lift N φ _ (group.quotient.mk N (finsupp.single r 1)) = val,
    --show group.quotient.lift N φ _ ⟦finsupp.single r 1⟧ = val,
    rw group.quotient.lift_mk',
    suffices : finsupp.prod (finsupp.single r (1:ℤ)) (λ (r : R), pow (φ₀ r)) = val,
      simpa [φ] using this,
    rw finsupp.prod_single_index,
      show φ₀ r ^ 0 = 1,refl,
    show (φ₀ r) * 1 = val,
    rw mul_one,
    dsimp [φ₀],
    rw Hval,
    refl,
  },
  have Hf1 : is_valuation f1 := valuation.valuation_of_valuation R f1 f2 ψ
                                  Hψ H12 (λ g h,iff.refl _) Hf2,
  existsi Hf1,
  exact valuation.le_of_le R f1 f2 ψ H12 (λ g h, iff.refl _),
end 

definition quot.mk {R : Type u1} [comm_ring R] [decidable_eq R] {Γ2 : Type u2} [linear_ordered_comm_group Γ2]
(f : R → option Γ2) [Hf : is_valuation f] : Spv R := ⟨λ r s, f r ≤ f s,
  begin
    rcases (value_group_universe R Γ2 f Hf) with ⟨Γ1,HΓ1,f1,Hf1,H12⟩,
    existsi Γ1,existsi HΓ1,
    letI : linear_ordered_comm_group Γ1 := HΓ1,
    let v : @valuation R _ Γ1 HΓ1 := {
      f := f1,
      ..Hf1,
    },
    existsi v,
    intros r s,
    show _ ↔ f1 r ≤ f1 s,
    rw H12 r s,
  end 
⟩

definition mk {R : Type u1} [comm_ring R] [decidable_eq R] {Γ2 : Type u2} [linear_ordered_comm_group Γ2]
(v : valuation R Γ2) : Spv R := quot.mk v.f

end Spv 

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
