import data.nat.prime
import algebra.group_power
import topology.algebra.ring
import topology.opens

import for_mathlib.prime
import for_mathlib.is_cover
import for_mathlib.sheaves.sheaf_of_topological_rings
import for_mathlib.sheaves.stalk_of_rings

import continuous_valuations
import Spa
import Huber_pair

universe u

open nat function
open topological_space

namespace sheaf_of_topological_rings

instance topological_space {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X) (U : opens X) :
topological_space (𝒪X.F.F U) := presheaf_of_topological_rings.topological_space_sections 𝒪X.F U

instance topological_ring {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X) (U : opens X) :
  topological_ring (𝒪X.F.F U) := presheaf_of_topological_rings.Ftop_ring 𝒪X.F U

instance topological_add_group {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X) (U : opens X) :
  topological_add_group (𝒪X.F.F U) := topological_ring.to_topological_add_group (𝒪X.F.F U)

--FIXME -- should be local
def uniform_space {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X) (U : opens X) :
  uniform_space (𝒪X.F.F U) := topological_add_group.to_uniform_space (𝒪X.F.F U)

end sheaf_of_topological_rings

section 𝒱
local attribute [instance] sheaf_of_topological_rings.uniform_space

/-- Wedhorn's category 𝒱 -/
structure 𝒱 (X : Type*) [topological_space X] :=
(𝒪X : sheaf_of_topological_rings X)
(complete : ∀ U : opens X, complete_space (𝒪X.F.F U))
(valuation : ∀ x : X, Spv (stalk_of_rings 𝒪X.to_presheaf_of_topological_rings.to_presheaf_of_rings x))
(local_stalks : ∀ x : X, is_local_ring (stalk_of_rings 𝒪X.to_presheaf_of_rings x))
(supp_maximal : ∀ x : X, ideal.is_maximal (_root_.valuation.supp (valuation x).out))

end 𝒱

/-- An auxiliary category 𝒞.  -/
structure 𝒞 (X : Type*) [topological_space X] :=
(𝒪X : presheaf_of_topological_rings X)
(valuation: ∀ x : X, Spv (stalk_of_rings 𝒪X.to_presheaf_of_rings x))

def 𝒱.to_𝒞 {X : Type*} [topological_space X] (F : 𝒱 X) : 𝒞 X :=
{ 𝒪X := F.𝒪X.to_presheaf_of_topological_rings,
  valuation := F.valuation}
/- todo :
Term of type 𝒞 for each Huber pair
Open set in X -> induced 𝒞 structure
morphisms and isomorphisms in 𝒞
definition of adic space
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
