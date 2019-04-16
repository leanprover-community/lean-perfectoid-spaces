/-
    Sheaf (of types).

    https://stacks.math.columbia.edu/tag/006S

    Author: Ramon Fernandez Mir
-/

import for_mathlib.sheaves.covering
import for_mathlib.sheaves.presheaf

universes u v

open topological_space lattice

section sheaf_condition

variables {α : Type u} [topological_space α]

-- Restriction map from U to U ∩ V.

def res_to_inter_left (F : presheaf α) (U V : opens α)
: (F U) → (F (U ∩ V)) :=
F.res U (U ∩ V) (set.inter_subset_left U V)

-- Restriction map from V to U ∩ V.

def res_to_inter_right (F : presheaf α) (U V : opens α)
: (F V) → (F (U ∩ V)) :=
F.res V (U ∩ V) (set.inter_subset_right U V)

-- Sheaf condition.

def locality (F : presheaf α) :=
∀ {U} (OC : covering U) (s t : F U),
(∀ i, F.res U (OC.Uis i) (subset_covering i) s =
      F.res U (OC.Uis i) (subset_covering i) t) →
s = t

def gluing (F : presheaf α) :=
∀ {U} (OC : covering U),
∀ (s : Π i, F (OC.Uis i)),
(∀ j k, res_to_inter_left F (OC.Uis j) (OC.Uis k) (s j) =
        res_to_inter_right F (OC.Uis j) (OC.Uis k) (s k)) →
∃ S, ∀ i, F.res U (OC.Uis i) (subset_covering i) S = s i

end sheaf_condition


-- Definition of a sheaf of types.

structure sheaf (α : Type u) [T : topological_space α] :=
(F        : presheaf α)
(locality : locality F)
(gluing   : gluing F)

section sheaf_of_types

variables {α : Type u} [T : topological_space α]
include T

instance sheaf.to_presheaf : has_coe (sheaf α) (presheaf α) :=
⟨λ S, S.F⟩

def is_sheaf (F : presheaf α) :=
locality F ∧ gluing F

end sheaf_of_types
