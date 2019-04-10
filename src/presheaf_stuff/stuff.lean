-- import algebraic_geometry.preordered_stalks
-- import category_theory.instances.TopCommRing

-- universes v u

-- open algebraic_geometry
-- open category_theory
-- open category_theory.instances

-- namespace algebraic_geometry.PresheafedSpace
-- -- We define a shorthand for the stalk at a point, computed in Types
-- def stalk' (X : PresheafedSpace.{v} TopCommRing.{v}) (x : X.X) :=
-- (TopCommRing.forget.map_presheaf.obj X).stalk x

-- -- And a short hand for the induced maps of (type-level) stalks
-- def stalk_map' {X Y : PresheafedSpace.{v} TopCommRing.{v}} (f : X ⟶ Y) (x : X.X) :
--   Y.stalk' (f x) → X.stalk' x :=
-- stalk_map (TopCommRing.forget.map_presheaf.map f) x

-- end algebraic_geometry.PresheafedSpace
