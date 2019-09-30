/-
  Sheaf of topological rings.
-/
import algebra.pi_instances

import sheaves.sheaf_of_rings
import sheaves.presheaf_of_topological_rings

universes u

-- A sheaf of topological rings is a sheaf of rings with the extra condition
-- that the map from 𝒪_X(U) to ∏𝒪_X(U_i) is a homeomorphism onto its image
-- (and not just continuous).

open topological_space presheaf_of_topological_rings

def sheaf.gluing_map {α : Type u} [topological_space α]
  (F : presheaf_of_topological_rings α) {U : opens α} (OC : covering U) :
  F U → {s : Π i, F (OC.Uis i) //
(∀ j k, res_to_inter_left F.to_presheaf (OC.Uis j) (OC.Uis k) (s j) =
        res_to_inter_right F (OC.Uis j) (OC.Uis k) (s k))} :=
λ S, ⟨λ i, F.res U (OC.Uis i) (subset_covering i) S, begin
  intros,
  unfold res_to_inter_right,
  unfold res_to_inter_left,
  rw ←F.to_presheaf.Hcomp',
  exact F.to_presheaf.Hcomp' U (OC.Uis k) _ _ _ S,
end⟩

def presheaf_of_topological_rings.homeo {α : Type u} [topological_space α]
  (F : presheaf_of_topological_rings α) :=
∀ {U} (OC : covering U), is_open_map (sheaf.gluing_map F OC)

structure sheaf_of_topological_rings (α : Type u) [T : topological_space α] :=
(F        : presheaf_of_topological_rings α)
(locality : locality F.to_presheaf) -- two sections which are locally equal are equal
(gluing   : gluing F.to_presheaf) -- a section can be defined locally
(homeo    : presheaf_of_topological_rings.homeo F) -- topology on sections is compatible with glueing

section sheaf_of_topological_rings

def sheaf_of_topological_rings.to_presheaf_of_topological_rings
  {α : Type u} [topological_space α] (S : sheaf_of_topological_rings α) :
(presheaf_of_topological_rings α) := S.F

def sheaf_of_topological_rings.to_presheaf_of_rings {α : Type u} [topological_space α]
  (F : sheaf_of_topological_rings α) : presheaf_of_rings α := F.F.to_presheaf_of_rings

def sheaf_of_topological_rings.to_sheaf_of_rings {α : Type u} [topological_space α]
  (F : sheaf_of_topological_rings α) : sheaf_of_rings α :=
{ F := {..F.F} ..F}

instance sheaf_of_topological_rings.to_presheaf {α : Type u} [topological_space α] :
  has_coe (sheaf_of_topological_rings α) (presheaf α) :=
⟨λ S, S.F.to_presheaf⟩

def is_sheaf_of_topological_rings {α : Type u} [topological_space α]
  (F : presheaf_of_topological_rings α) :=
locality F.to_presheaf ∧ gluing F.to_presheaf ∧ presheaf_of_topological_rings.homeo F

end sheaf_of_topological_rings
