import algebra.group_power
import topology.algebra.ring
import topology.opens
import category_theory.category
import category_theory.full_subcategory

import for_mathlib.open_embeddings
import for_mathlib.topological_groups

import sheaves.f_map

import continuous_valuations
import rat_open_data_completion
import stalk_valuation
import Huber_pair

/-!
# Adic spaces

Adic spaces were introduced by Huber in [Huber]. They form a very general category of objects
suitable for p-adic geometry.

In this file we define the category of adic spaces. The category of schemes (from algebraic
geometry) may provide some useful intuition for the definition.
One defines the category of “ringed spaces”, and for every commutative ring R
a ringed space Spec(R). A scheme is a ringed space that admits a cover by subspaces that
are isomorphic to spaces of the form Spec(R) for some ring R.

Similarly, for adic spaces we need two ingredients: a category CLVRS,
and the so-called ”adic spectrum” Spa(_), which is defined in Spa.lean.
An adic space is an object of CLVRS is that admits a cover by subspaces of the form Spa(A).

The main bulk of this file consists in setting up the category that we called CLVRS,
and that never got a proper name in the literature. (For example, Wedhorn calls this category `𝒱`.)

CLVRS (complete locally valued ringed space) is the category of topological spaces endowed
with a sheaf of complete topological rings and (an equivalence class of) valuations on the stalks
(which are required to be local rings; moreover the support of the valuation must be
the maximal ideal of the stalk).

Once we have the category CLVRS in place, the definition of adic spaces is made in
a couple of lines.
-/

universe u

open nat function
open topological_space
open spa

open_locale classical

/-- A convenient auxiliary category whose objects are topological spaces equipped with
a presheaf of topological rings and on each stalk (considered as abstract ring) an
equivalence class of valuations. The point of this category is that the local isomorphism
between a general adic space and an affinoid model Spa(A) can be checked in this category.
-/
structure PreValuedRingedSpace :=
(space : Type u)
[top   : topological_space space]
(presheaf : presheaf_of_topological_rings.{u u} space)
(valuation : ∀ x : space, Spv (stalk_of_rings presheaf.to_presheaf_of_rings x))

namespace PreValuedRingedSpace

variables (X : PreValuedRingedSpace.{u})

/-- Coercion from a PreValuedRingedSpace to the underlying topological space.-/
instance : has_coe_to_sort PreValuedRingedSpace.{u} :=
{ S := Type u,
  coe := λ X, X.space }

-- Adding the fact that the underlying space of a PreValuedRingedSpace is a topological
-- space, to the type class inference system
instance : topological_space X := X.top

end PreValuedRingedSpace

/- Remainder of this file:

* Morphisms and isomorphisms in PreValuedRingedSpace.
* Open set in X -> restrict structure to obtain object of PreValuedRingedSpace
* Definition of adic space

* A morphism in PreValuedRingedSpace is a map of topological spaces,
  and an f-map of presheaves, such that the induced
  map on the stalks pulls one valuation back to the other.
-/


namespace PreValuedRingedSpace
open category_theory

/-- A morphism of pre-valued ringed spaces is a morphism of the structure presheaves
(of topological rings, hence *continuous* on sections),
such that for every point x in the domain the induced map on stalks pulls valuation on the stalk
back to the valuation of the stalk on the image of x.-/
structure hom (X Y : PreValuedRingedSpace.{u}) :=
(fmap : presheaf_of_topological_rings.f_map X.presheaf Y.presheaf)
(stalk : ∀ x : X,
  Spv.comap (stalk_map fmap.to_presheaf_of_rings_f_map x) (X.valuation x) = Y.valuation (fmap.f x))

attribute [simp] hom.stalk

/-- A morphism of pre-valued ringed spaces is determined by the data
of the morphism of the structure presheaves.-/
@[extensionality]
lemma hom_ext {X Y : PreValuedRingedSpace.{u}} (f g : hom X Y) :
  f.fmap = g.fmap → f = g :=
by { cases f, cases g, tidy }

/--The identity morphism of a pre-valued ringed space.-/
def id (X : PreValuedRingedSpace.{u}) : hom X X :=
{ fmap := presheaf_of_topological_rings.f_map_id _,
  stalk := λ x, by { dsimp, simp, } }

@[simp] lemma id_fmap {X : PreValuedRingedSpace} :
  (id X).fmap = presheaf_of_topological_rings.f_map_id _ := rfl

/--The composition of morphisms of pre-valued ringed spaces.-/
def comp {X Y Z : PreValuedRingedSpace.{u}} (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ fmap := f.fmap.comp g.fmap,
  stalk := λ x,
  begin
    dsimp, simp only [comp_app, stalk_map.stalk_map_comp', hom.stalk, Spv.comap_comp],
    dsimp, simp only [hom.stalk],
  end }

/--Pre-valued ringed spaces form a large category.-/
instance large_category : large_category (PreValuedRingedSpace.{u}) :=
{ hom  := hom,
  id   := id,
  comp := λ X Y Z f g, comp f g,
  id_comp' :=
  begin
    intros X Y f, ext, dsimp [comp],
    exact presheaf_of_rings.f_map.id_comp _,
  end,
  comp_id' :=
  begin
    intros X Y f, ext, dsimp [comp],
    exact presheaf_of_rings.f_map.comp_id _,
  end }

end PreValuedRingedSpace

/--If U is an open subset of a pre-valued ringed space X, then there is a natural way
to view U as a pre-valued ringed space by restricting the structure presheaf from X.-/
noncomputable instance PreValuedRingedSpace.restrict {X : PreValuedRingedSpace.{u}} :
  has_coe (opens X) PreValuedRingedSpace :=
{ coe := λ U,
  { space := U,
    top := by apply_instance,
    presheaf := presheaf_of_topological_rings.restrict U X.presheaf,
    valuation :=
      λ u, Spv.mk (valuation.comap (presheaf_of_rings.restrict_stalk_map _ _) (X.valuation u).out) } }

namespace sheaf_of_topological_rings

/-- The sections of a sheaf of topological rings form a uniform space.
When this is made an instance, beware of diamonds.-/
def uniform_space {X : Type u} [topological_space X] (𝒪X : sheaf_of_topological_rings X)
  (U : opens X) : uniform_space (𝒪X.F.F U) :=
topological_add_group.to_uniform_space (𝒪X.F.F U)

end sheaf_of_topological_rings

section
local attribute [instance] sheaf_of_topological_rings.uniform_space

/--Category of topological spaces endowed with a sheaf of complete topological rings
and (an equivalence class of) valuations on the stalks (which are required to be local
rings; moreover the support of the valuation must be the maximal ideal of the stalk).
Wedhorn calls this category `𝒱`.-/
structure CLVRS :=
(space : Type) -- change this to (Type u) to enable universes
[top   : topological_space space]
(sheaf : sheaf_of_topological_rings.{0 0} space)
(complete : ∀ U : opens space, complete_space (sheaf.F.F U))
(valuation : ∀ x : space, Spv (stalk_of_rings sheaf.to_presheaf_of_topological_rings.to_presheaf_of_rings x))
(local_stalks : ∀ x : space, is_local_ring (stalk_of_rings sheaf.to_presheaf_of_rings x))
(supp_maximal : ∀ x : space, ideal.is_maximal (_root_.valuation.supp (valuation x).out))

end

namespace CLVRS
open category_theory

/--A CLVRS is naturally a pre-valued ringed space.-/
def to_PreValuedRingedSpace (X : CLVRS) : PreValuedRingedSpace.{0} :=
{ presheaf := _, ..X }

/--The coercion from a CLVRS to a pre-valued ringed space.-/
instance : has_coe CLVRS PreValuedRingedSpace.{0} :=
⟨to_PreValuedRingedSpace⟩

/--CLVRS is a full subcategory of PreValuedRingedSpace.-/
instance : large_category CLVRS := induced_category.category to_PreValuedRingedSpace

/-
Remark: One can show that for every morphism in CLVRS,
the induced maps on stalks are local ring morphisms.
Sketch of proof: the valuation on the source pulls back to the valuation on the target,
and by assumption `supp_maximal` this means that the maximal ideal on the target
is mapped into the maximal ideal on the source.
-/

end CLVRS

/--The adic spectrum of a Huber pair.-/
noncomputable def Spa (A : Huber_pair) : PreValuedRingedSpace :=
{ space     := spa A,
  presheaf  := spa.presheaf_of_topological_rings A,
  valuation := λ x, Spv.mk (spa.presheaf.stalk_valuation x) }

open lattice

-- Notation for the proposition that an isomorphism exists between A and B
notation A `≊` B := nonempty (A ≅ B)

namespace CLVRS

/--A CLVRS is an adic space if every point has an open neighbourhood that is isomorphic
to the adic spectrum of a Huber pair.-/
def is_adic_space (X : CLVRS) : Prop :=
∀ x : X, ∃ (U : opens X) (R : Huber_pair), x ∈ U ∧ (Spa R ≊ U)

end CLVRS

/--A CLVRS is an adic space if every point has an open neighbourhood that is isomorphic
to the adic spectrum of a Huber pair.-/
def AdicSpace := {X : CLVRS // X.is_adic_space}

namespace AdicSpace
open category_theory

/--The category of adic spaces is the full subcategory of CLVRS that
consists of the objects that are adic spaces.-/
instance : large_category AdicSpace := category_theory.full_subcategory _

end AdicSpace
