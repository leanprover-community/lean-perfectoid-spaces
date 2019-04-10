import category_theory.category

universes u

namespace category_theory

variables (C : Type u) [𝒞 : small_category C]
include 𝒞

-- The versions of these that Reid defined just give existential statements,
-- which are harder to work with.
class is_filtered' extends inhabited C :=
(cocone_objs : ∀ (X Y : C), Σ (Z : C), (X ⟶ Z) × (Y ⟶ Z))
(cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), { p : Σ Z, Y ⟶ Z // f ≫ p.2 = g ≫ p.2 })

end category_theory
