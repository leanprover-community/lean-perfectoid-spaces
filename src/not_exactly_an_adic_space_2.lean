import data.nat.prime
import algebra.group_power
import topology.algebra.ring
import topology.opens
import algebraic_geometry.preordered_stalks
import category_theory.instances.TopCommRing

import for_mathlib.prime
import for_mathlib.is_cover

import continuous_valuations
import Spa
import Huber_pair

universes u v

open algebraic_geometry
open category_theory
open category_theory.instances
open category_theory.limits

namespace algebraic_geometry.PresheafedSpace
-- We define a shorthand for the stalk at a point, computed in Types
def stalk' (X : PresheafedSpace.{v} TopCommRing.{v}) (x : X.X) :=
(TopCommRing.forget.map_presheaf.obj X).stalk x

-- And a short hand for the induced maps of (type-level) stalks
def stalk_map' {X Y : PresheafedSpace.{v} TopCommRing.{v}} (f : X ⟶ Y) (x : X.X) :
  Y.stalk' (f x) → X.stalk' x :=
stalk_map (TopCommRing.forget.map_presheaf.map f) x

end algebraic_geometry.PresheafedSpace

open algebraic_geometry.PresheafedSpace

structure whatsit extends PresheafedSpace.{v} TopCommRing.{v} :=
(preorder : Π x : X, preorder (to_PresheafedSpace.stalk' x))

instance stalk_preorder (X : whatsit.{v}) (x : X.X) : preorder (X.to_PresheafedSpace.stalk' x) :=
X.preorder x

structure hom (F G : whatsit.{v}) :=
(hom : F.to_PresheafedSpace ⟶ G.to_PresheafedSpace)
(monotone : Π (x : F.X) (a b : G.to_PresheafedSpace.stalk' (PresheafedSpace.hom.f hom x)),
   (a ≤ b) ↔ ((stalk_map' hom x) a ≤ (stalk_map' hom x) b))
.

-- FIXME can't tag this with @[extensionality]?
lemma hom.ext {F G : whatsit.{v}} {f g : hom F G} (w : f.hom = g.hom) : f = g :=
begin
  cases f, cases g,
  congr; assumption
end


-- We need two lemmas about `stalk_map'`:
section

@[simp] lemma stalk_map'_id (F : PresheafedSpace.{v} TopCommRing.{v}) (x : F.X) :
  stalk_map' (𝟙 F) x = 𝟙 (F.stalk' x) :=
begin
  dsimp [stalk_map', stalk'],
  -- because of tangled type dependencies, we're going to have to give the original proof all over again
  sorry
end
@[simp] lemma stalk_map'_comp {F G H : PresheafedSpace.{v} TopCommRing.{v}} (α : F ⟶ G) (β : G ⟶ H) (x : F.X) :
  stalk_map' (α ≫ β) x =
    begin
      have p := (stalk_map' β (α x) : H.stalk' (β (α x)) ⟶ G.stalk' (α x)),
      have q := (stalk_map' α x : G.stalk' (α x) ⟶ F.stalk' x),
      exact q ∘ p
    end :=
sorry
end

def hom.id (F : whatsit.{v}) : hom F F :=
{ hom := 𝟙 F.to_PresheafedSpace,
  monotone := λ x a b, by simp,  }

def hom.comp (F G H : whatsit.{v}) (α : hom F G) (β : hom G H) : hom F H :=
{ hom := α.hom ≫ β.hom,
  monotone := λ x a b,
  begin
    simp,
    transitivity,
    apply β.monotone,
    apply α.monotone,
  end  }

section
local attribute [simp] id comp
instance : category whatsit.{v} :=
{ hom := hom,
  id := hom.id,
  comp := hom.comp,
  comp_id' := λ X Y f, sorry,
  id_comp' := λ X Y f, sorry,
  assoc' := λ W X Y Z f g h, sorry }
end
