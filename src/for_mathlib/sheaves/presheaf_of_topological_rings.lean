/-
  Presheaf of toplogical rings.

-/

import topology.algebra.ring
import for_mathlib.sheaves.presheaf_of_rings

universes u v

open topological_space

-- Definition of a presheaf of topological rings.

structure presheaf_of_topological_rings (α : Type u) [topological_space α]
extends presheaf_of_rings α :=
(Ftop : ∀ (U), topological_space (F U))
(Ftop_ring : ∀ (U), topological_ring (F U))
(res_continuous : ∀ (U V) (HVU : V ⊆ U), continuous (res U V HVU))

instance presheaf_of_topological_rings.has_coe {α : Type u} [topological_space α] :
  has_coe (presheaf_of_topological_rings α) (presheaf α) :=
⟨λ F, F.to_presheaf⟩

instance presheaf_of_topological_rings.topological_space_sections {α : Type u} [topological_space α]
  (F : presheaf_of_topological_rings α) (U : opens α) : topological_space (F U) :=
F.Ftop U

attribute [instance] presheaf_of_topological_rings.Ftop
attribute [instance] presheaf_of_topological_rings.Ftop_ring

namespace presheaf_of_topological_rings

variables {α : Type u} {β : Type v} [topological_space α] [topological_space β]

-- Morphism of presheaf of topological rings.

structure morphism (F G : presheaf_of_topological_rings α)
  extends presheaf.morphism F.to_presheaf G.to_presheaf :=
(ring_homs : ∀ (U), is_ring_hom (map U))
(continuous_homs : ∀ (U), continuous (map U))

infix `⟶`:80 := morphism

def identity (F : presheaf_of_topological_rings α) : F ⟶ F :=
{ ring_homs := λ U, is_ring_hom.id,
  continuous_homs := λ U, continuous_id,
  ..presheaf.id F.to_presheaf }

-- Isomorphic presheaves of rings.

structure iso (F G : presheaf_of_topological_rings α) :=
(mor : F ⟶ G)
(inv : G ⟶ F)
(mor_inv_id : mor.to_morphism ⊚ inv.to_morphism = presheaf.id F.to_presheaf)
(inv_mor_id : inv.to_morphism ⊚ mor.to_morphism = presheaf.id G.to_presheaf)

local infix `≅`:80 := λ A B, nonempty (iso A B)

end presheaf_of_topological_rings
