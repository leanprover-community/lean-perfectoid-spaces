import group_theory.quotient_group

universes u₁ u₂ u₃

open is_group_hom quotient_group function

variables {G₁ : Type u₁} [group G₁]
variables {G₂ : Type u₂} [group G₂]
variables (φ : G₁ → G₂) [is_group_hom φ]

def inc : quotient (ker φ) → G₂ :=
lift _ φ $ λ g, (mem_ker φ).mp

lemma inc_mk (g : G₁) : (inc φ) g = φ g :=
lift_mk _ _ _

lemma inc_mk' (g : G₁) : (inc φ) (mk g) = φ g :=
lift_mk' _ _ _

instance : is_group_hom (inc φ) :=
quotient_group.is_group_hom_quotient_lift _ _ _

lemma inc_injective : injective (inc φ) :=
assume a b, quotient.induction_on₂' a b $
assume a b (h : φ a = φ b), quotient.sound' $
show a⁻¹ * b ∈ ker φ,
by rw [mem_ker φ, is_group_hom.mul φ, ← h, is_group_hom.inv φ, inv_mul_self]

section
variables {N₁ : set G₁} [normal_subgroup N₁]
variables {N₂ : set G₂} [normal_subgroup N₂]

instance map_is_group_hom (h : N₁ ⊆ φ ⁻¹' N₂) : is_group_hom (map _ _ φ h) :=
quotient_group.is_group_hom_quotient_lift _ _ _

end
