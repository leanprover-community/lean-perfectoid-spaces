import category_theory.instances.Top.open_nhds
import for_mathlib.filtered

universe v

open category_theory
open category_theory.instances
open topological_space
open topological_space.open_nhds

variables {X : Top.{v}}

instance (x : X) : has_inter (open_nhds x)ᵒᵖ :=
{ inter := λ U V, op ⟨(unop U).1 ∩ (unop V).1, ⟨(unop U).2, (unop V).2⟩⟩ }

-- Gross!
instance (x : X) (U V : (open_nhds x)ᵒᵖ) : subsingleton (U ⟶ V) :=
⟨λ f g, begin dsimp [opposite] at U V, cases U, cases V, dsimp [(⟶)] at f g, cases f, cases f, cases g, cases g, refl, end⟩

instance (x : X) : is_filtered' (open_nhds x)ᵒᵖ :=
{ default := op ⟨⊤, set.mem_univ X⟩,  -- we should have a lattice structure on open_nhds x, and just use ⊤
  cocone_objs := λ U V, ⟨U ∩ V, ⟨begin /- gross!-/ dsimp [opposite] at *, cases U, cases V, dsimp [(⟶)], split, split, intros x h, dsimp [(∩)] at h, cases h, exact h_left, end,
                                 begin /- gross!-/ dsimp [opposite] at *, cases U, cases V, dsimp [(⟶)], split, split, intros x h, dsimp [(∩)] at h, cases h, exact h_right, end ⟩ ⟩ ,
  cocone_maps := λ U V f g, ⟨⟨V, 𝟙 V⟩, begin dsimp, simp, apply subsingleton.elim end⟩ }

def bar (x : X) {U : opens X} (h : x ∈ U) : ((opens.to_Top X).obj U) := ⟨x, h⟩

-- def foo (x : X) (U : opens X) (h : x ∈ U) : open_nhds (bar x h) ⥤ open_nhds x :=
-- { obj := λ V, ⟨⟨V.val.val, sorry⟩, sorry⟩,
--   map := sorry, }
