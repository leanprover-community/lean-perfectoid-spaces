import data.nat.prime
import algebra.group_power
import topology.algebra.ring
import topology.opens

import for_mathlib.prime
import for_mathlib.is_cover
import for_mathlib.sheaves.sheaf_of_topological_rings

import continuous_valuations
import Spa
import Huber_pair

universe u

open nat function
open topological_space

instance meh {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X) (U : opens X) :
topological_space (𝒪X.F.F U) := presheaf_of_topological_rings.topological_space_sections 𝒪X.F U

instance meh' {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X) (U : opens X) :
  topological_ring (𝒪X.F.F U) := presheaf_of_topological_rings.Ftop_ring 𝒪X.F U

instance meh''' {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X) (U : opens X) :
  topological_add_group (𝒪X.F.F U) := topological_ring.to_topological_add_group (𝒪X.F.F U)

instance meh'' {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X) (U : opens X) :
  uniform_space (𝒪X.F.F U) := topological_add_group.to_uniform_space (𝒪X.F.F U)

/-- Wedhorn's category 𝒱 -/
structure 𝒱 (X : Type*) [topological_space X] :=
(𝒪X : sheaf_of_topological_rings X)
(complete : ∀ U : opens X, complete_space (𝒪X.F.F U))


/-- An auxiliary category 𝒞.  -/
structure 𝒞 (X : Type*) [topological_space X]
-- :=
--(𝓞X : presheaf of rings)
--(complete : 𝓞X U is a complete topological ring)
--(local : stalks are local)
--(val : valuation on each stalk with support the max ideal)

/-
We denote by 𝓥pre the category of tuples X = (X, O X , (v x ) x∈X ), where
(a) X is a topological space,
(b) 𝓞_X is a presheaf of complete topological rings on X such that the stalk 𝓞_X,x of
𝓞_X (considered as a presheaf of rings) is a local ring,
(c) v_x is an equivalence class of valuations on the stalk 𝓞_X,x such that supp(v_x) is the
maximal ideal of 𝓞_X,x .

Wedhorn p76 shows how Spa(A) gives an object of this for A a Huber pair
-/

--definition affinoid_adic_space (A : Huber_pair) : 𝓥pre := sorry

-- unwritten -- it's a full subcat of 𝓥pre
class preadic_space (X : Type*) extends topological_space X

-- not logically necessary but should be easy
instance (A : Huber_pair) : preadic_space (Spa A) := sorry

-- attribute [class] _root_.is_open

instance preadic_space_restriction {X : Type*} [preadic_space X] {U : opens X} :
  preadic_space U.val := sorry

-- unwritten
class adic_space (X : Type*) extends preadic_space X
-- note Wedhorn remark 8.19; being a sheaf of top rings involves a topological condition

-- a preadic_space_equiv is just an isom in 𝓥pre, or an isomorphism of preadic spaces.
-- unwritten
structure preadic_space_equiv (X Y : Type*) [AX : preadic_space X] [AY : preadic_space Y] extends equiv X Y

definition is_preadic_space_equiv (X Y : Type*) [AX : preadic_space X] [AY : preadic_space Y] :=
  nonempty (preadic_space_equiv X Y)

definition preadic_space_pullback {X : Type*} [preadic_space X] (U : set X) := {x : X // x ∈ U}

instance pullback_is_preadic_space {X : Type*} [preadic_space X] (U : set X) : preadic_space (preadic_space_pullback U) := sorry

-- notation `is_open` := _root_.is_open
