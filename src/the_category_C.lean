/- For want of a better name, C is the category whose objects are a topological space,
   a presheaf of topological rings, and a binary relation (we might make it a valuation)
   on each stalk.
-/

import algebraic_geometry.stalks
import category_theory.limits.types
import category_theory.instances.TopCommRing
import topology.opens

import for_mathlib.opens
import for_mathlib.open_nhds
import for_mathlib.open_embeddings

universes v u

open algebraic_geometry
open category_theory
open category_theory.instances
open category_theory.limits
open topological_space

open algebraic_geometry.PresheafedSpace

structure relation_stalks (F : PresheafedSpace.{v} (Type v)) :=
(relation : Π x : F.X, (F.stalk x) → (F.stalk x) → Prop)

def preserves_relation {F G : PresheafedSpace.{v} (Type v)} (F_r : relation_stalks F)
  (G_r : relation_stalks G) (f : F ⟶ G) : Prop :=
∀ (x : F.X) (a b : G.stalk (f.f x)),
   (G_r.relation (f.f x) a b) ↔ (F_r.relation x ((stalk_map f x) a) ((stalk_map f x) b))

structure C extends PresheafedSpace.{v} TopCommRing.{v} :=
(s : relation_stalks ((TopCommRing.forget.map_presheaf).obj to_PresheafedSpace))

structure C_hom (F G : C.{v}) :=
(f : F.to_PresheafedSpace ⟶ G.to_PresheafedSpace)
(s : preserves_relation F.s G.s ((TopCommRing.forget.map_presheaf).map f))
.

@[extensionality]
lemma C_hom.ext {F G : C.{v}} {f g : C_hom F G} (w : f.f = g.f) : f = g :=
begin
  cases f, cases g,
  congr; assumption
end

open algebraic_geometry.presheaf_on_space

@[simp] lemma stalk_map.id' {F : C.{v}} (x : F.X) :
  (stalk_map ((functor.map_presheaf TopCommRing.forget).map (𝟙 (F.to_PresheafedSpace))) x) = id :=
by refine stalk_map.id _ _

@[simp] lemma stalk_map.comp' {F G H : C.{v}} (α : C_hom F G) (β : C_hom G H) (x : F.X) :
  stalk_map ((TopCommRing.forget.map_presheaf).map (α.f ≫ β.f)) x =
    (stalk_map ((TopCommRing.forget.map_presheaf).map β.f) (α.f x) :
      ((TopCommRing.forget.map_presheaf).obj H.to_PresheafedSpace).stalk (β.f.f (α.f.f x)) ⟶
      ((TopCommRing.forget.map_presheaf).obj G.to_PresheafedSpace).stalk (α.f.f x)) ≫
    (stalk_map ((TopCommRing.forget.map_presheaf).map α.f) x :
      ((TopCommRing.forget.map_presheaf).obj G.to_PresheafedSpace).stalk (α.f.f x) ⟶
      ((TopCommRing.forget.map_presheaf).obj F.to_PresheafedSpace).stalk x) :=
begin
  convert stalk_map.comp _ _ _,
  erw category_theory.functor.map_comp,
  erw category_theory.functor.map_comp,
end
.

def C_hom.id (F : C.{v}) : C_hom F F :=
{ f := 𝟙 F.to_PresheafedSpace,
  s := λ x a b,
    begin
      show (F.s).relation x a b ↔ (F.s).relation x
        (stalk_map ((functor.map_presheaf TopCommRing.forget).map (𝟙 (F.to_PresheafedSpace))) x a)
        (stalk_map ((functor.map_presheaf TopCommRing.forget).map (𝟙 (F.to_PresheafedSpace))) x b),
      simp,
    end }

def C_hom.comp (F G H : C.{v}) (α : C_hom F G) (β : C_hom G H) : C_hom F H :=
{ f := α.f ≫ β.f,
  s := λ x a b,
  begin
    suffices : (H.s).relation ((((functor.map_presheaf TopCommRing.forget).map (α.f ≫ β.f)).f) x) a b ↔
    (F.s).relation x
      (stalk_map ((functor.map_presheaf TopCommRing.forget).map (α.f)) x
         (stalk_map ((functor.map_presheaf TopCommRing.forget).map (β.f)) ((α.f) x) a))
      (stalk_map ((functor.map_presheaf TopCommRing.forget).map (α.f)) x
         (stalk_map ((functor.map_presheaf TopCommRing.forget).map (β.f)) ((α.f) x) b)),
      simpa,
    transitivity,
    apply β.s,
    apply α.s,
  end  }

section
local attribute [simp] C_hom.id C_hom.comp PresheafedSpace.id_c PresheafedSpace.comp_c
instance : category C.{v} :=
{ hom := C_hom,
  id := C_hom.id,
  comp := C_hom.comp,
  comp_id' := λ X Y f,
  begin
    ext,
    { dsimp,
      simp,
      erw category_theory.functor.map_id,
      erw category.comp_id,
      dsimp [opposite] at X_1,
      cases X_1,
      dsimp,
      erw category_theory.functor.map_id,
      simp,
      refl, },
    refl,
  end,
  id_comp' := λ X Y f,
  begin
    ext,
    { dsimp,
      simp,
      erw category_theory.functor.map_id,
      erw category.comp_id, },
    refl,
  end, }
end
.

open topological_space

def inclusion (X : Top.{v}) (U : opens X) :
  opens ((opens.to_Top X).obj U) ⥤ opens X :=
functor.is_open_map.map (is_open_map_of_open U.2)

namespace algebraic_geometry.PresheafedSpace
variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

def restrict (X : PresheafedSpace.{v} C) (U : opens X) : PresheafedSpace.{v} C :=
{ X := (opens.to_Top X.X).obj U,
  𝒪 := (inclusion X.X U).op ⋙ X.𝒪 }

-- jmc: This deserves better treatment in the lib
def to_op_unop (V : Cᵒᵖ) : V ⟶ (op (unop V)) := 𝟙 V

def restrict.ι (X : PresheafedSpace.{v} C) (U : opens X) :
  X.restrict U ⟶ X :=
{ f := ⟨subtype.val, continuous_subtype_val⟩,
  c :=
  { app := λ V, X.𝒪.map (to_op_unop V ≫ has_hom.hom.op (ulift.up $ plift.up $
            set.image_preimage_subset subtype.val (unop V).val)),
    naturality' :=
    begin
      intros V₁ V₂ i,
      erw ← X.𝒪.map_comp,
      erw ← X.𝒪.map_comp,
      congr' 1,
    end } }

section
variables {D : Type u} [𝒟 : category.{v+1} D]
include 𝒟
-- Usually it would be dangerous to state an equality between PresheafedSpaces, but this is definitional so hopefully it's okay!
def map_presheaf_restrict (X : PresheafedSpace.{v} C) (U : opens X.X) (F : C ⥤ D) :
  (F.map_presheaf.obj X).restrict U = F.map_presheaf.obj (X.restrict U) :=
rfl
end

section
variables [has_colimits.{v} C]
def restrict_stalk' (X : PresheafedSpace.{v} C) (U : opens X) (x : (X.restrict U)) :
  stalk X (x.val) ⟶ stalk (X.restrict U) x :=
stalk_map (restrict.ι X U) x

-- TODO should construct an iso, but for tonight we just need one direction!
def restrict_stalk (X : PresheafedSpace.{v} C) (U : opens X) (x : (X.restrict U)) :
  stalk (X.restrict U) x ⟶ stalk X (restrict.ι X U x) :=
colimit.desc.{v} ((open_nhds.inclusion _).op ⋙ (X.restrict U).𝒪)
{ X := stalk X (restrict.ι X U x),
  ι :=
  { app := λ (V : (open_nhds.open_nhds x)ᵒᵖ),
    begin
      refine _ ≫ (colimit.ι ((open_nhds.inclusion _).op ⋙ X.𝒪) _),
      { refine ((functor.is_open_map.open_nhds.map _ _).op).obj V,
        exact (is_open_map_of_open U.2) },
      { dsimp [restrict], exact X.𝒪.map (𝟙 _).op }
    end,
    naturality' := λ V₁ V₂ XYZZY,
    begin
      dsimp,
      erw [← category.assoc, ← X.𝒪.map_comp, X.𝒪.map_id, category.comp_id, category.comp_id,
        category.id_comp, ← functor.op_map],
      rw show
        (X.𝒪).map ((functor.op (inclusion (X.X) U)).map ((functor.op (open_nhds.inclusion x)).map XYZZY)) =
        ((open_nhds.inclusion ((restrict.ι X U) x)).op ⋙ X.𝒪).map
          ((functor.is_open_map.open_nhds.map _ x).map (XYZZY.unop)).op,
      { erw functor.comp_map },
      apply colimit.w
    end } }
end
end algebraic_geometry.PresheafedSpace

def restrict (X : C) (U : opens X.X) : C :=
{ X := (X.to_PresheafedSpace.restrict U).X,
  𝒪 := (X.to_PresheafedSpace.restrict U).𝒪,
  s :=
  { relation := λ x a b,
    begin
      have a' := ((TopCommRing.forget.map_presheaf.obj X.to_PresheafedSpace).restrict_stalk U x) a,
      have b' := ((TopCommRing.forget.map_presheaf.obj X.to_PresheafedSpace).restrict_stalk U x) b,
      exact X.s.relation x.val a' b'
    end } }
