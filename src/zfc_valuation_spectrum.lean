-- This file is never used -- it was KMB trying to get everything
-- to fit into "Type".
#exit 

import valuation_spectrum data.equiv.basic

definition zfc.Spv (A : Type) [comm_ring A] : Type := 
  {ineq : A → A → Prop // ∃ v : valuations A, ∀ r s : A, ineq r s ↔ v.f r ≤ v.f s}

variables {A : Type} [comm_ring A]

--set_option pp.implicit true 
--set_option pp.notation false
def to_fun (A : Type) [comm_ring A] := quotient.lift (λ v,(⟨λ r s, valuations.f v r ≤ valuations.f v s,⟨v,λ r s,iff.rfl⟩⟩ : zfc.Spv A)) 
      (λ v w H,subtype.eq $ funext $ λ r, funext $ λ s, propext $ H r s)

theorem to_fun.bijective : function.bijective (to_fun A) := ⟨
  λ vs ws,quotient.induction_on₂ vs ws $ λ v w H,quotient.sound $ λ r s,iff_of_eq $ congr_fun (congr_fun (subtype.mk.inj H) r) s--(congr_fun (congr_fun (subtype.mk.inj H) r) s)))
    ,λ ⟨ineq,⟨v,Hv⟩⟩,⟨⟦v⟧,subtype.eq $ funext $ λ r,funext $ λ s,propext (Hv r s).symm⟩⟩

noncomputable lemma Spv_equiv (A : Type) [comm_ring A] : equiv (Spv A) (zfc.Spv A) :=
  equiv.of_bijective (to_fun.bijective)
