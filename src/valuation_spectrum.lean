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

/-
theorem value_group_universe (R : Type u1) [comm_ring R] [decidable_eq R] (Γ2 : Type u2) [linear_ordered_comm_group Γ2]
  (f2 : R → option Γ2) (Hf2 : is_valuation f2) : 
∃ (Γ1 : Type u1) [linear_ordered_comm_group Γ1], by exactI ∃ (f1 : R → option Γ1) (Hf1 : is_valuation f1),
  (∀ r s : R, f1 r ≤ f1 s ↔ f2 r ≤ f2 s) ∧ value_group_f f1 = set.univ := 
-/
definition valuation.minimal_value_group {R : Type u1} [comm_ring R] [decidable_eq R] 
  {Γ2 : Type u2} [linear_ordered_comm_group Γ2]
  (f2 : R → option Γ2) [Hf2 : is_valuation f2] : 
Type u1 :=
begin
  let FG : Type u1 := multiplicative (R →₀ ℤ), -- free ab group on R
  let φ₀ : R → Γ2 := λ r, option.get_or_else (f2 r) 1, 
  let φ : FG → Γ2 := λ f, finsupp.prod f (λ r n,(φ₀ r) ^ n),
  have Hprod:  ∀ (a : R) (b₁ b₂ : ℤ), φ₀ a ^ (b₁ + b₂) = φ₀ a ^ b₁ * φ₀ a ^ b₂ := 
    λ a b₁ b₂, gpow_add _ _ _,
  letI Hφ : is_group_hom φ :=
  { mul := λ a b,finsupp.prod_add_index (λ a,rfl) Hprod,
  },
  exact quotient_group (is_group_hom.ker φ) 
end 

instance valuation.minimal_value_group_is_linear_ordered_comm_group
  {R : Type u1} [comm_ring R] [decidable_eq R] 
  {Γ2 : Type u2} [linear_ordered_comm_group Γ2]
  (f2 : R → option Γ2) [Hf2 : is_valuation f2] : 
linear_ordered_comm_group (valuation.minimal_value_group f2) :=
begin
  let FG : Type u1 := multiplicative (R →₀ ℤ), -- free group on R
  let φ₀ : R → Γ2 := λ r, option.get_or_else (f2 r) 1, 
  let φ : FG → Γ2 := λ f, finsupp.prod f (λ r n,(φ₀ r) ^ n), 
  have Hprod:  ∀ (a : R) (b₁ b₂ : ℤ), φ₀ a ^ (b₁ + b₂) = φ₀ a ^ b₁ * φ₀ a ^ b₂ := 
    λ a b₁ b₂, gpow_add _ _ _,
  letI Hφ : is_group_hom φ :=
  { mul := λ a b,finsupp.prod_add_index (λ a,rfl) Hprod,
  },
  let N := is_group_hom.ker φ,
  let Γ1 := quotient_group N,
  let ψ : Γ1 → Γ2 := group.quotient.lift N φ (λ _,(is_group_hom.mem_ker φ).1),
  have Hψ : function.injective ψ := group.quotient.injective_ker_lift φ,
  --  begin
  --  funext,apply propext,
  --  show x ∈ N ↔ _,
  --  exact is_group_hom.mem_ker φ,
  --  end,
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
  exact Γ1order,
end

<<<<<<< HEAD
definition Spv (A : Type) [comm_ring A] : Type 1 := quotient (valuations.setoid A)
=======
definition valuation.minimal_valuation 
  {R : Type u1} [comm_ring R] [decidable_eq R] 
  {Γ2 : Type u2} [linear_ordered_comm_group Γ2]
  (f2 : R → option Γ2) [Hf2 : is_valuation f2] : 
R → option (valuation.minimal_value_group f2) :=
begin
  let FG : Type u1 := multiplicative (R →₀ ℤ), -- free group on R
  let φ₀ : R → Γ2 := λ r, option.get_or_else (f2 r) 1, 
  let φ : FG → Γ2 := λ f, finsupp.prod f (λ r n,(φ₀ r) ^ n), 
  have Hprod:  ∀ (a : R) (b₁ b₂ : ℤ), φ₀ a ^ (b₁ + b₂) = φ₀ a ^ b₁ * φ₀ a ^ b₂ := 
    λ a b₁ b₂, gpow_add _ _ _,
  letI Hφ : is_group_hom φ :=
  { mul := λ a b,finsupp.prod_add_index (λ a,rfl) Hprod,
  },
  let N := is_group_hom.ker φ,
  let Γ1 := quotient_group N,
  let ψ : Γ1 → Γ2 := group.quotient.lift N φ (λ _,(is_group_hom.mem_ker φ).1),
  have Hψ : function.injective ψ := group.quotient.injective_ker_lift φ,
  --  begin
  --  funext,apply propext,
  --  show x ∈ N ↔ _,
  --  exact is_group_hom.mem_ker φ,
  --  end,
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
  let f1 : R → option Γ1 := (λ r, 
  option.rec_on (f2 r) (none : option Γ1) 
    (λ (r' : Γ2), (group.quotient.mk N (finsupp.single r (1 : ℤ)) : option Γ1))),
  exact f1,
end 
>>>>>>> master

instance valuation.minimal_valuation_is_valuation
  {R : Type u1} [comm_ring R] [decidable_eq R] 
  {Γ2 : Type u2} [linear_ordered_comm_group Γ2]
  (f2 : R → option Γ2) [Hf2 : is_valuation f2] : 
is_valuation (valuation.minimal_valuation f2) :=
begin
  let FG : Type u1 := multiplicative (R →₀ ℤ), -- free group on R
  let φ₀ : R → Γ2 := λ r, option.get_or_else (f2 r) 1, 
  let φ : FG → Γ2 := λ f, finsupp.prod f (λ r n,(φ₀ r) ^ n), 
  have H0 : ∀ (a : R), φ₀ a ^ 0 = 1 := λ a,rfl,
  have Hprod:  ∀ (a : R) (b₁ b₂ : ℤ), φ₀ a ^ (b₁ + b₂) = φ₀ a ^ b₁ * φ₀ a ^ b₂ := 
    λ a b₁ b₂, gpow_add _ _ _,
  letI Hφ : is_group_hom φ :=
  { mul := λ a b,finsupp.prod_add_index H0 Hprod,
  },
  let N := is_group_hom.ker φ,
  let Γ1 := quotient_group N,
  let ψ : Γ1 → Γ2 := group.quotient.lift N φ (λ _,(is_group_hom.mem_ker φ).1),
  have Hψ : function.injective ψ := group.quotient.injective_ker_lift φ,
  --  begin
  --  funext,apply propext,
  --  show x ∈ N ↔ _,
  --  exact is_group_hom.mem_ker φ,
  --  end,
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
  let f1 : R → option Γ1 := (λ r, 
  option.rec_on (f2 r) (none : option Γ1) 
    (λ (r' : Γ2), (group.quotient.mk N (finsupp.single r (1 : ℤ)) : option Γ1))),
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
  exact Hf1,
end

definition valuation.minimal_valuation_equiv
  {R : Type u1} [comm_ring R] [decidable_eq R] 
  {Γ2 : Type u2} [linear_ordered_comm_group Γ2]
  (f2 : R → option Γ2) [Hf2 : is_valuation f2] : 
let f1 := valuation.minimal_valuation f2 in
(∀ r s : R, f1 r ≤ f1 s ↔ f2 r ≤ f2 s) :=
begin
  let FG : Type u1 := multiplicative (R →₀ ℤ), -- free group on R
  let φ₀ : R → Γ2 := λ r, option.get_or_else (f2 r) 1, 
  let φ : FG → Γ2 := λ f, finsupp.prod f (λ r n,(φ₀ r) ^ n), 
  have H0 : ∀ (a : R), φ₀ a ^ 0 = 1 := λ a,rfl,
  have Hprod:  ∀ (a : R) (b₁ b₂ : ℤ), φ₀ a ^ (b₁ + b₂) = φ₀ a ^ b₁ * φ₀ a ^ b₂ := 
    λ a b₁ b₂, gpow_add _ _ _,
  letI Hφ : is_group_hom φ :=
  { mul := λ a b,finsupp.prod_add_index H0 Hprod,
  },
  let N := is_group_hom.ker φ,
  let Γ1 := quotient_group N,
  let ψ : Γ1 → Γ2 := group.quotient.lift N φ (λ _,(is_group_hom.mem_ker φ).1),
  have Hψ : function.injective ψ := group.quotient.injective_ker_lift φ,
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
  let f1 : R → option Γ1 := (λ r, 
  option.rec_on (f2 r) (none : option Γ1) 
    (λ (r' : Γ2), (group.quotient.mk N (finsupp.single r (1 : ℤ)) : option Γ1))),
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
    exact valuation.le_of_le R f1 f2 ψ H12 (λ g h, iff.refl _),
end 

definition quot.mk {R : Type u1} [comm_ring R] [decidable_eq R] {Γ2 : Type u2} [linear_ordered_comm_group Γ2]
(f : R → option Γ2) [Hf : is_valuation f] : Spv R := ⟨λ r s, f r ≤ f s,
  begin
    let Γ1 := valuation.minimal_value_group f,
    let f1 := valuation.minimal_valuation f,
    have H12 := valuation.minimal_valuation_equiv f,
    let v : valuation R Γ1 := {
      f := f1,
      ..(valuation.minimal_valuation_is_valuation f)
    },
    existsi Γ1,
    existsi (valuation.minimal_value_group_is_linear_ordered_comm_group f),
    existsi v,
    intros r s,
    show _ ↔ f1 r ≤ f1 s,
    rw H12 r s,
  end 
⟩

definition mk {R : Type u1} [comm_ring R] [decidable_eq R] {Γ2 : Type u2} [linear_ordered_comm_group Γ2]
(v : valuation R Γ2) : Spv R := quot.mk v.f

<<<<<<< HEAD
variables {A : Type} [comm_ring A] -- fix a ring A

local attribute [instance] classical.prop_decidable

-- Should this lemma be in the file valuations.lean ??
lemma gt_zero_iff_equiv_gt_zero (s : A) (v w : valuations A) (H : v ≈ w) :
v(s) > 0 ↔ w(s) > 0 :=
begin
  rw [←not_iff_not,
      iff.intro le_of_not_gt not_lt_of_ge,
      iff.intro le_of_not_gt not_lt_of_ge,
      ←v.Hf.map_zero,
      ←w.Hf.map_zero],
  exact H s 0,
=======
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
-- need value_group_f f1 = set.univ

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
>>>>>>> master
end 
-/

namespace Spv 

variables {A : Type*} [comm_ring A]

<<<<<<< HEAD
/-- The basic open subset for the topology on Spv(A).-/
definition basic_open (r s : A) : set (Spv A) :=
-- on representatives
quotient.lift (λ v : valuations A, v(r) ≤ v(s) ∧ v(s) > 0)
-- independence of representative
  (λ v w H,
  begin
    dsimp,
    rw [H r s, gt_zero_iff_equiv_gt_zero s v w H]
  end)

instance (A : Type) [comm_ring A] : topological_space (Spv A) :=
=======
definition basic_open (r s : A) : set (Spv A) := 
{v | v.val r s ∧ ¬ v.val s 0}

instance (A : Type*) [comm_ring A] : topological_space (Spv A) :=
>>>>>>> master
topological_space.generate_from {U : set (Spv A) | ∃ r s : A, U = basic_open r s}

end Spv 
