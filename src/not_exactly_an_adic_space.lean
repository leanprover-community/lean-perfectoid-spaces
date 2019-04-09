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

universe u

open algebraic_geometry
open category_theory
open category_theory.instances

structure thingummy :=
-- First, we need a topological space, with a presheaf of topological commutative rings:
(presheaf_of_rings : PresheafedSpace.{u} TopCommRing.{u})
-- Second, we need a topological space, with a presheaf of types, equipped with
-- a preorder on each stalk.
(preordered_stalks : PreorderPresheaf)
-- But those two things aren't independent: it's the same presheaf of types in both cases.
(compatible :
  (TopCommRing.forget.map_presheaf).obj presheaf_of_rings ≅ preordered_stalks.to_PresheafedSpace)

structure thingummy_hom (X Y : thingummy)
-- A map should consist of a morphism of presheaves of rings (this gadget respects topologies, etc)
(ring_hom : X.presheaf_of_rings ⟶ Y.presheaf_of_rings)
-- And it should also respect the preorders we're putting on the stalks:
(preorder_hom : X.preordered_stalks ⟶ Y.preordered_stalks)
-- But again those two things duplicate lots of data, so we need to check they are the same on
-- the underlying presheaves of types:
(compatible : (TopCommRing.forget.map_presheaf).map ring_hom = X.compatible.hom ≫ (PreorderPresheaf.hom.hom preorder_hom) ≫ Y.compatible.inv)

-- Finally, since everything in sight already had a category structure, we can assemble on here:
instance : category thingummy :=
{ hom := thingummy_hom,
  id := sorry,
  comp := sorry, }
