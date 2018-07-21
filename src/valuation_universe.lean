import valuations 
import for_mathlib.option_inj 

universes u1 u2 

theorem option.group_hom   
  (Γ1 : Type u1) [linear_ordered_comm_group Γ1]
  (Γ2 : Type u2) [linear_ordered_comm_group Γ2] 
  (ψ : Γ1 → Γ2)
  [Hgψ : is_group_hom ψ]
  (og oh : option Γ1) :
option.map ψ (og * oh) = option.map ψ og * option.map ψ oh :=
begin
  cases hog : og; cases hih : oh;try {refl},
  show some (ψ (val * val_1)) = some ((ψ val) * (ψ val_1)),
  apply option.some_inj.2,
  exact is_group_hom.mul ψ val val_1,
end 

theorem option.le 
  (Γ1 : Type u1) [linear_ordered_comm_group Γ1]
  (Γ2 : Type u2) [linear_ordered_comm_group Γ2] 
  (ψ : Γ1 → Γ2)
  (Hineqψ : ∀ g h : Γ1, g ≤ h ↔ ψ g ≤ ψ h)
  (og oh : option Γ1) :
og ≤ oh ↔ option.map ψ og ≤ option.map ψ oh :=
begin
  cases hog : og; cases hih : oh;try {refl},
  exact Hineqψ val val_1,
end 

theorem valuation.le_of_le (R : Type u1) 
  {Γ1 : Type u1} [linear_ordered_comm_group Γ1]
  {Γ2 : Type u2} [linear_ordered_comm_group Γ2] 
  (f1 : R → option Γ1)
  (f2 : R → option Γ2) 
  (ψ : Γ1 → Γ2)
  (H12 : ∀ (r : R), option.map ψ (f1 r) = f2 r)
  (Hle : ∀ g h : Γ1, g ≤ h ↔ ψ g ≤ ψ h)
  (r s : R) : 
f1 r ≤ f1 s ↔ f2 r ≤ f2 s :=
begin
  rw ←H12 r, rw ←H12 s,
  cases hr : (f1 r) with g;cases hs : (f1 s) with h; try {refl},
  exact Hle g h,
end 

theorem valuation.valuation_of_valuation (R : Type u1) [comm_ring R]
  {Γ1 : Type u1} [linear_ordered_comm_group Γ1]
  {Γ2 : Type u2} [linear_ordered_comm_group Γ2] 
  (f1 : R → option Γ1)
  (f2 : R → option Γ2) 
  (ψ : Γ1 → Γ2)
  [Hgψ : is_group_hom ψ]
  (Hiψ : function.injective ψ)
  (H12 : ∀ (r : R), option.map ψ (f1 r) = f2 r)
  (Hle : ∀ g h : Γ1, g ≤ h ↔ ψ g ≤ ψ h)
  (Hvf2 : is_valuation f2) :
is_valuation f1 :=
begin
  constructor,
  { show f1 0 = 0,
    have H0 : f2 0 = 0 := Hvf2.1,
    rw ←H12 0 at H0,
    change option.map ψ (f1 0) = none at H0,
    cases h1 : f1 0,refl,
    exfalso,
    rw h1 at H0,
    revert H0,
    exact dec_trivial,
  },
  { show f1 1 = 1,
    have H0 : f2 1 = 1 := Hvf2.2,
    rw ←H12 1 at H0,
    cases h1 : f1 1,
    { exfalso,
      rw h1 at H0,
      unfold option.map at H0,
      unfold option.bind at H0,
      exact option.no_confusion H0,
    },
    rw h1 at H0,
    change some (ψ val) = some 1 at H0,
    congr,
    apply Hiψ,
    rw option.some_inj.1 H0,
    rw is_group_hom.one ψ 
  },
  { intros r s,
    apply option.map_inj Hiψ,
    rw H12 (r * s),
    rw Hvf2.3,
    rw [←H12 r,←H12 s],
    symmetry,
    exact option.group_hom _ _ _ _ _,
  },
  { intros r s,
    cases is_valuation.map_add f2 r s,
    { left,
      rw [←H12 r,←H12 (r+s)] at h,
      rwa (option.le _ _ ψ _ _ _),
      exact Hle
    },
    { right,
      rw [←H12 s,←H12 (r+s)] at h,
      rwa (option.le _ _ ψ _ _ _),
      exact Hle
    },
  }
end 