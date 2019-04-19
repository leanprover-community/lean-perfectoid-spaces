import data.nat.prime
import algebra.group_power
import topology.algebra.ring
import topology.opens

import for_mathlib.prime
import for_mathlib.is_cover
import for_mathlib.sheaves.sheaf_of_topological_rings

import continuous_valuations
import r_o_d_completion
import Huber_pair

universe u

open nat function
open topological_space

namespace sheaf_of_topological_rings

instance topological_space {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X)
  (U : opens X) :
  topological_space (𝒪X.F.F U) := presheaf_of_topological_rings.topological_space_sections 𝒪X.F U

instance topological_ring {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X)
  (U : opens X) :
  topological_ring (𝒪X.F.F U) := presheaf_of_topological_rings.Ftop_ring 𝒪X.F U

instance topological_add_group {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X)
  (U : opens X) :
  topological_add_group (𝒪X.F.F U) :=
topological_ring.to_topological_add_group (𝒪X.F.F U)

def uniform_space {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X)
  (U : opens X) : uniform_space (𝒪X.F.F U) :=
topological_add_group.to_uniform_space (𝒪X.F.F U)

end sheaf_of_topological_rings

section 𝒱
local attribute [instance] sheaf_of_topological_rings.uniform_space

/-- Wedhorn's category 𝒱 -/
structure 𝒱 (X : Type*) [topological_space X] :=
(ℱ : sheaf_of_topological_rings X)
(complete : ∀ U : opens X, complete_space (ℱ.F.F U))
(valuation : ∀ x : X, Spv (stalk_of_rings ℱ.to_presheaf_of_topological_rings.to_presheaf_of_rings x))
(local_stalks : ∀ x : X, is_local_ring (stalk_of_rings ℱ.to_presheaf_of_rings x))
(supp_maximal : ∀ x : X, ideal.is_maximal (_root_.valuation.supp (valuation x).out))

end 𝒱

/-- An auxiliary category 𝒞.  -/
structure 𝒞 (X : Type*) [topological_space X] :=
(F : presheaf_of_topological_rings X)
(valuation: ∀ x : X, Spv (stalk_of_rings F.to_presheaf_of_rings x))

def 𝒱.to_𝒞 {X : Type*} [topological_space X] (ℱ : 𝒱 X) : 𝒞 X :=
{ F := ℱ.ℱ.to_presheaf_of_topological_rings,
  valuation := ℱ.valuation}

noncomputable def 𝒞.Spa (A : Huber_pair)
  (hA : topological_space.is_topological_basis (rational_basis' A)) :
  𝒞 (Spa A) :=
{ F := Spa.presheaf_of_topological_rings A,
  valuation := λ x, Spv.mk (Spa.presheaf.stalk_valuation x hA) }

/- Remainder of this file:

morphisms and isomorphisms in 𝒞.
Open set in X -> induced 𝒞 structure
definition of adic space

A morphism in 𝒞 is a map of top spaces, an f-map of presheaves, such that the induced
map on the stalks pulls one valuation back to the other.
-/

def continuous.comap {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {f : X → Y} (hf : continuous f) (V : opens Y) : opens X := ⟨f ⁻¹' V.1, hf V.1 V.2⟩

def continuous.comap_mono {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {f : X → Y} (hf : continuous f) {V W : opens Y} (hVW : V ⊆ W) : hf.comap V ⊆ hf.comap W :=
λ _ h, hVW h



structure presheaf_of_rings.f_hom
  {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  (F : presheaf_of_rings X) (G : presheaf_of_rings Y) :=
(f : X → Y)
(hf : continuous f)
(f_flat : ∀ V : opens Y, G V → F (hf.comap V))
(presheaf_f_flat : ∀ V W : opens Y, ∀ (hWV : W ⊆ V),
  ∀ s : G V, F.res _ _ (hf.comap_mono hWV) (f_flat V s) = f_flat W (G.res V W hWV s))

structure presheaf_of_topological_rings.f_hom
  {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  (F : presheaf_of_topological_rings X) (G : presheaf_of_topological_rings Y) :=
(f : X → Y)
(hf : continuous f)
(f_flat : ∀ V : opens Y, G V → F (hf.comap V))
(cont_f_flat : ∀ V : opens Y, continuous (f_flat V))
(presheaf_f_flat : ∀ V W : opens Y, ∀ (hWV : W ⊆ V),
  ∀ s : G V, F.res _ _ (hf.comap_mono hWV) (f_flat V s) = f_flat W (G.res V W hWV s))

def presheaf_of_topological_rings.f_hom.to_presheaf_of_rings_f_hom
  {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {F : presheaf_of_topological_rings X} {G : presheaf_of_topological_rings Y}
  (f : presheaf_of_topological_rings.f_hom F G) :
  presheaf_of_rings.f_hom F.to_presheaf_of_rings G.to_presheaf_of_rings :=
{ ..f}

-- need a construction `stalk_map` attached to an f-hom; should follow from UMP
-- Need this before we embark on 𝒞.map

--set_option pp.all true
local attribute [instance, priority 0] classical.prop_decidable
noncomputable def stalk_map {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {F : presheaf_of_rings X} {G : presheaf_of_rings Y} (f : presheaf_of_rings.f_hom F G)
  (x : X) : stalk_of_rings G (f.f x) → stalk_of_rings F x :=
to_stalk.rec G (f.f x) (stalk_of_rings F x)
  (λ V hfx s, ⟦⟨f.hf.comap V, hfx, f.f_flat V s⟩⟧)
  (λ V W H r hfx, quotient.sound begin
    use [f.hf.comap V, hfx, set.subset.refl _, f.hf.comap_mono H],
    erw F.to_presheaf.Hid,
    symmetry,
    apply f.presheaf_f_flat
  end )

-- not right -- just committing before reboot
structure 𝒞.map {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  (F : 𝒞 X) (G : 𝒞 Y) :=
(fmap : presheaf_of_topological_rings.f_hom F.F G.F)
(stalk : ∀ x : X, stalk_map fmap.to_presheaf_of_rings_f_hom x 0 = 0)

def 𝒞.res {X : Type*} [topological_space X] (U : opens X) (F : 𝒞 X) : 𝒞 U :=
sorry

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
