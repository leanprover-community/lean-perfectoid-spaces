import group_theory.quotient_group

universes u₁ u₂ u₃

-- The contents of this file are currently being PR'd to mathlib

-- Start of PR #764

open is_group_hom quotient_group function

variables {G₁ : Type u₁} [group G₁]
variables {G₂ : Type u₂} [group G₂]
variables (φ : G₁ → G₂) [is_group_hom φ]

def ker_lift : quotient (ker φ) → G₂ :=
lift _ φ $ λ g, (mem_ker φ).mp

lemma ker_lift_mk (g : G₁) : (ker_lift φ) g = φ g :=
lift_mk _ _ _

lemma ker_lift_mk' (g : G₁) : (ker_lift φ) (mk g) = φ g :=
lift_mk' _ _ _

instance : is_group_hom (ker_lift φ) :=
quotient_group.is_group_hom_quotient_lift _ _ _

lemma injective_ker_lift' : injective (ker_lift φ) :=
assume a b, quotient.induction_on₂' a b $
assume a b (h : φ a = φ b), quotient.sound' $
show a⁻¹ * b ∈ ker φ,
by rw [mem_ker φ, is_group_hom.mul φ, ← h, is_group_hom.inv φ, inv_mul_self]

-- end of PR #764

section
variables {N₁ : set G₁} [normal_subgroup N₁]
variables {N₂ : set G₂} [normal_subgroup N₂]

-- the following instance is in PR #761

instance map_is_group_hom (h : N₁ ⊆ φ ⁻¹' N₂) : is_group_hom (map _ _ φ h) :=
quotient_group.is_group_hom_quotient_lift _ _ _

end
