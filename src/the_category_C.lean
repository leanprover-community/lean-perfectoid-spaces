import algebraic_geometry.stalks
import category_theory.limits.types
import category_theory.instances.TopCommRing
import topology.opens

universes v u

open algebraic_geometry
open category_theory
open category_theory.instances
open category_theory.limits

open algebraic_geometry.PresheafedSpace

structure relation_stalks (F : PresheafedSpace.{v} (Type v)) :=
(relation : Π x : F.X, (F.stalk x) → (F.stalk x) → Prop)

def preserves_relation {F G : PresheafedSpace.{v} (Type v)} (F_r : relation_stalks F) (G_r : relation_stalks G) (f : F ⟶ G) : Prop :=
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
    (stalk_map ((TopCommRing.forget.map_presheaf).map β.f) (α.f x) : ((TopCommRing.forget.map_presheaf).obj H.to_PresheafedSpace).stalk (β.f.f (α.f.f x)) ⟶ ((TopCommRing.forget.map_presheaf).obj G.to_PresheafedSpace).stalk (α.f.f x)) ≫
    (stalk_map ((TopCommRing.forget.map_presheaf).map α.f) x : ((TopCommRing.forget.map_presheaf).obj G.to_PresheafedSpace).stalk (α.f.f x) ⟶ ((TopCommRing.forget.map_presheaf).obj F.to_PresheafedSpace).stalk x) :=
begin
  convert stalk_map.comp _ _ _,
  erw category_theory.functor.map_comp,
  erw category_theory.functor.map_comp,
end
.

def C_hom.id (F : C.{v}) : C_hom F F :=
{ f := 𝟙 F.to_PresheafedSpace,
  s := λ x a b, begin dsimp at *, simp, end,  }

def C_hom.comp (F G H : C.{v}) (α : C_hom F G) (β : C_hom G H) : C_hom F H :=
{ f := α.f ≫ β.f,
  s := λ x a b,
  begin
    simp,
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
