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

namespace sheaf_of_topological_rings

-- Maybe we could make this an instance?
def uniform_space {X : Type u} [topological_space X] (𝒪X : sheaf_of_topological_rings X)
  (U : opens X) : uniform_space (𝒪X.F.F U) :=
topological_add_group.to_uniform_space (𝒪X.F.F U)

end sheaf_of_topological_rings

/-- A convenient auxiliary category whose objects are topological spaces equipped with
a presheaf of topological rings and on each stalk (considered as abstract ring) an
equivalence class of valuations. The point of this category is that the local isomorphism
between a general adic space and an affinoid model Spa(A) can be checked in this category.
-/
structure PreValuedRingedSpace :=
(space : Type u)
(top   : topological_space space)
(presheaf : presheaf_of_topological_rings.{u u} space)
(valuation : ∀ x : space, Spv (stalk_of_rings presheaf.to_presheaf_of_rings x))

namespace PreValuedRingedSpace

variables (X : PreValuedRingedSpace.{u})

/-- Coercion from a PreValuedRingedSpace to the underlying topological space-/
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

structure hom (X Y : PreValuedRingedSpace.{u}) :=
(fmap : presheaf_of_topological_rings.f_map X.presheaf Y.presheaf)
(stalk : ∀ x : X, ((X.valuation x).out.comap (stalk_map fmap.to_presheaf_of_rings_f_map x)).is_equiv
  (Y.valuation (fmap.f x)).out)

lemma hom_ext {X Y : PreValuedRingedSpace.{u}} (f g : hom X Y) :
  f.fmap = g.fmap → f = g :=
by { cases f, cases g, tidy }

def id (X : PreValuedRingedSpace.{u}) : hom X X :=
{ fmap := presheaf_of_topological_rings.f_map_id,
  stalk := λ x,
  begin
    show valuation.is_equiv
    ((Spv.out (X.valuation x)).comap
       (stalk_map
          (presheaf_of_rings.f_map_id X.presheaf.to_presheaf_of_rings)
          x))
    (Spv.out (X.valuation ((λ (x : X), x) x))),
    simp only [stalk_map_id' X.presheaf.to_presheaf_of_rings x],
    convert valuation.is_equiv.refl,
    ext, refl,
  end }

def comp {X Y Z : PreValuedRingedSpace.{u}} (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ fmap := presheaf_of_topological_rings.f_map_comp f.fmap g.fmap,
  stalk := λ x, begin refine valuation.is_equiv.trans _ (g.stalk (f.fmap.f x)),
    let XXX := f.stalk x,
    let YYY := valuation.is_equiv.comap (stalk_map (presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map (g.fmap))
          ((presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map (f.fmap)).f x)) XXX,
    show valuation.is_equiv _ ((Spv.out (Y.valuation ((f.fmap).f x))).comap _),
    refine valuation.is_equiv.trans _ YYY,
    rw ←valuation.comap_comp,
    suffices : (stalk_map
          (presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map
             (presheaf_of_topological_rings.f_map_comp (f.fmap) (g.fmap)))
          x) = (stalk_map (presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map (f.fmap)) x ∘
          stalk_map (presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map (g.fmap))
            ((presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map (f.fmap)).f x)),
      simp [this],
    rw ←stalk_map_comp',
    refl,
  end }

instance large_category : large_category (PreValuedRingedSpace.{u}) :=
{ hom  := hom,
  id   := id,
  comp := λ X Y Z f g, comp f g,
  id_comp' :=
  begin
    intros X Y f,
    apply hom_ext,
    rcases f with ⟨⟨f, f_cont, f_flat, f_hom, f_flat_cont, hf⟩, f_stalk⟩,
    rcases X with ⟨X, top, ⟨⟨presheaf, ps_ring, res_hom⟩, ps_top, ps_top_ring, res_cont⟩, val⟩,
    dsimp [id, comp, continuous.comap, presheaf_of_rings.f_map_id, presheaf_of_rings.f_map_comp,
      presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map,
      presheaf_of_topological_rings.f_map_comp, presheaf_of_topological_rings.f_map_id] at *,
    clear f_stalk,
    congr,
    funext V s,
    resetI,
    exact congr_fun (presheaf.Hid ⟨f ⁻¹' V.val, _⟩) (f_flat V s)
  end,
  comp_id' :=
  begin
    intros X Y f,
    apply hom_ext,
    cases f, cases f_fmap,
    dsimp,
    cases Y, cases Y_presheaf, cases Y_presheaf__to_presheaf_of_rings,
    cases Y_presheaf__to_presheaf_of_rings__to_presheaf,
    dsimp [id, comp, continuous.comap, presheaf_of_rings.f_map_id, presheaf_of_rings.f_map_comp,
      presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map,
      presheaf_of_topological_rings.f_map_comp, presheaf_of_topological_rings.f_map_id] at *,
    congr,
    clear f_stalk, funext,
    have H2 : f_fmap_f_flat V
      (Y_presheaf__to_presheaf_of_rings__to_presheaf_res V V _ s) =
      f_fmap_f_flat V s,
      rw Y_presheaf__to_presheaf_of_rings__to_presheaf_Hid V, refl,
    convert H2,
      apply opens.ext,refl,
      apply opens.ext,refl,
  end }

end PreValuedRingedSpace

noncomputable instance PreValuedRingedSpace.restrict {X : PreValuedRingedSpace.{u}} :
  has_coe (opens X) PreValuedRingedSpace :=
{ coe := λ U,
  { space := U,
    top := by apply_instance,
    presheaf := presheaf_of_topological_rings.restrict U X.presheaf,
    valuation :=
      λ u, Spv.mk (valuation.comap (presheaf_of_rings.restrict_stalk_map _ _) (X.valuation u).out) } }

section
local attribute [instance] sheaf_of_topological_rings.uniform_space

/--Category of topological spaces endowed with a sheaf of complete topological rings
and (an equivalence class of) valuations on the stalks (which are required to be local
rings; moreover the support of the valuation must be the maximal ideal of the stalk).
Wedhorn calls this category `𝒱`.-/
structure CLVRS :=
(space : Type) -- change this to (Type u) to enable universes
(top   : topological_space space)
(sheaf : sheaf_of_topological_rings.{0 0} space)
(complete : ∀ U : opens space, complete_space (sheaf.F.F U))
(valuation : ∀ x : space, Spv (stalk_of_rings sheaf.to_presheaf_of_topological_rings.to_presheaf_of_rings x))
(local_stalks : ∀ x : space, is_local_ring (stalk_of_rings sheaf.to_presheaf_of_rings x))
(supp_maximal : ∀ x : space, ideal.is_maximal (_root_.valuation.supp (valuation x).out))

end

namespace CLVRS
open category_theory

def to_PreValuedRingedSpace (X : CLVRS) : PreValuedRingedSpace.{0} :=
{ presheaf := _, ..X }

instance : has_coe CLVRS PreValuedRingedSpace.{0} :=
⟨to_PreValuedRingedSpace⟩

instance : large_category CLVRS := induced_category.category to_PreValuedRingedSpace

end CLVRS

/--The adic spectrum of a Huber pair.-/
noncomputable def Spa (A : Huber_pair) : PreValuedRingedSpace :=
{ space     := spa A,
  top       := by apply_instance,
  presheaf  := spa.presheaf_of_topological_rings A,
  valuation := λ x, Spv.mk (spa.presheaf.stalk_valuation x) }

open lattice

-- Notation for the proposition that an isomorphism exists between A and B
notation A `≊` B := nonempty (A ≅ B)

namespace CLVRS

def is_adic_space (X : CLVRS) : Prop :=
∀ x : X, ∃ (U : opens X) (R : Huber_pair), x ∈ U ∧ (Spa R ≊ U)

end CLVRS

def AdicSpace := {X : CLVRS // X.is_adic_space}

namespace AdicSpace
open category_theory

instance : large_category AdicSpace := category_theory.full_subcategory _

end AdicSpace

-- #doc_blame!
