import .relation_on_colimit
import algebraic_geometry.stalks
import for_mathlib.open_nhds

universes v u

open category_theory
open category_theory.instances
open algebraic_geometry
open topological_space
open topological_space.open_nhds

variables (X : Top.{v})
variables (F : presheaf_on_space (Type v) X)

def stalk_desc₂ (Y : Type v) (x : X)
  (f : Π (U : (open_nhds x)ᵒᵖ), ((inclusion x).op ⋙ F).obj U → ((inclusion x).op ⋙ F).obj U → Y)
  (w : Π (U U' : (open_nhds x)ᵒᵖ) (k : U ⟶ U'), (λ a b, f U' (((inclusion x).op ⋙ F).map k a) (((inclusion x).op ⋙ F).map k b)) = f U)
  : F.stalk x ⟶ (F.stalk x ⟶ Y) :=
desc₂ ((inclusion x).op ⋙ F) Y f w
