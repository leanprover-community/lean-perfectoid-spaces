#exit

-- I am not sure we care about le_mul_equivs so I'll just leave them here under the #exit

section linear_ordered_comm_group

structure le_mul_equiv (X : Type*) (Y : Type*)
  [has_le X] [has_mul X] [has_le Y] [has_mul Y]
   extends le_equiv X Y :=
(mul_hom : is_mul_hom to_fun)

infix ` ≃≤* `:50 := le_mul_equiv

def le_mul_equiv.to_mul_equiv {X : Type*} {Y : Type*} [has_le X] [has_mul X] [has_le Y] [has_mul Y]
  (h : X ≃≤* Y) : X ≃* Y := { ..h}

structure linear_ordered_comm_group_equiv (X : Type*) (Y : Type*)
  [linear_ordered_comm_group X] [linear_ordered_comm_group Y] extends le_mul_equiv X Y

end linear_ordered_comm_group

namespace le_mul_equiv
variables {X} {Y} {Z}

@[refl] def refl (X : Type*) [has_le X] : X ≃≤ X :=
{ le_hom := λ _ _, iff.rfl,
  ..equiv.refl _}

@[symm] def symm (h : X ≃≤ Y) : Y ≃≤  X :=
{ le_hom := λ x₁ x₂, begin convert (h.le_hom (h.to_equiv.symm x₁) (h.to_equiv.symm x₂)).symm,
    exact (h.right_inv x₁).symm, exact (h.right_inv x₂).symm end,
  ..h.to_equiv.symm
}

@[trans] def trans (h1 : X ≃≤ Y) (h2 : Y ≃≤ Z) : X ≃≤ Z :=
{ le_hom := λ x₁ x₂, iff.trans (h1.le_hom x₁ x₂) (h2.le_hom (h1.to_fun x₁) (h1.to_fun x₂)),
  ..equiv.trans h1.to_equiv h2.to_equiv
}

end le_mul_equiv
