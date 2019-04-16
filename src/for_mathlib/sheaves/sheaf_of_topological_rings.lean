/-
  Sheaf of topological rings.
-/

import for_mathlib.sheaves.sheaf_of_rings
import for_mathlib.sheaves.presheaf_of_topological_rings

universes u

-- A sheaf of topological rings is a sheaf of rings with the extra condition
-- that the map from 𝒪_X(U) to ∏𝒪_X(U_i) is a homeomorphism onto its image
-- (and not just continuous).

structure sheaf_of_topological_rings (α : Type u) [T : topological_space α] :=
(F        : sheaf_of_rings α)
(locality : locality F.to_presheaf)
(gluing   : gluing F.to_presheaf)

section sheaf_of_rings

instance sheaf_of_rings.to_presheaf_of_rings {α : Type u} [topological_space α]
: has_coe (sheaf_of_rings α) (presheaf_of_rings α) :=
⟨λ S, S.F⟩

instance sheaf_of_rings.to_presheaf {α : Type u} [topological_space α]
: has_coe (sheaf_of_rings α) (presheaf α) :=
⟨λ S, S.F.to_presheaf⟩

def is_sheaf_of_rings {α : Type u} [topological_space α] (F : presheaf_of_rings α) :=
  locality F.to_presheaf
∧ gluing F.to_presheaf

end sheaf_of_rings
