/-
  Presheaf (of types).

  https://stacks.math.columbia.edu/tag/006D

  Author: Ramon Fernandez Mir
-/

import topology.basic
import topology.opens

universes u v

-- Definition of a presheaf.

open topological_space lattice

structure presheaf (α : Type u) [topological_space α] :=
(F     : opens α → Type v)
(res   : ∀ (U V) (HVU : V ⊆ U), F U → F V)
(Hid   : ∀ (U), res U U (set.subset.refl U) = id)
(Hcomp : ∀ (U V W) (HWV : W ⊆ V) (HVU : V ⊆ U),
  res U W (set.subset.trans HWV HVU) = res V W HWV ∘ res U V HVU)

namespace presheaf

variables {α : Type u} [topological_space α]

instance : has_coe_to_fun (presheaf α) :=
{ F := λ _, opens α → Type v,
  coe := presheaf.F }

-- Simplification lemmas for Hid and Hcomp.

@[simp] lemma Hcomp' (F : presheaf α) :
∀ (U V W) (HWV : W ⊆ V) (HVU : V ⊆ U) (s : F U),
  (F.res U W (set.subset.trans HWV HVU)) s =
  (F.res V W HWV) ((F.res U V HVU) s) :=
λ U V W HWV HVU s, by rw F.Hcomp U V W HWV HVU

@[simp] lemma Hid' (F : presheaf α) :
∀ (U) (s : F U),
  (F.res U U (set.subset.refl U)) s = s :=
λ U s, by rw F.Hid U; simp

-- Morphism of presheaves.

structure morphism (F G : presheaf α) :=
(map      : ∀ (U), F U → G U)
(commutes : ∀ (U V) (HVU : V ⊆ U),
  (G.res U V HVU) ∘ (map U) = (map V) ∘ (F.res U V HVU))

infix `⟶`:80 := morphism

section morphism

def comp {F G H : presheaf α} (fg : F ⟶ G) (gh : G ⟶ H) : F ⟶ H :=
{ map := λ U, gh.map U ∘ fg.map U,
  commutes := λ U V HVU,
    begin
      rw [←function.comp.assoc, gh.commutes U V HVU], symmetry,
      rw [function.comp.assoc, ←fg.commutes U V HVU]
    end }

infix `⊚`:80 := comp

def id (F : presheaf α) : F ⟶ F :=
{ map := λ U, id,
  commutes := λ U V HVU, by simp, }

structure iso (F G : presheaf α) :=
(mor : F ⟶ G)
(inv : G ⟶ F)
(mor_inv_id : mor ⊚ inv = id F)
(inv_mor_id : inv ⊚ mor = id G)

local infix `≅`:80 := iso

end morphism

end presheaf
