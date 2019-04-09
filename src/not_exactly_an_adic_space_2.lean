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
