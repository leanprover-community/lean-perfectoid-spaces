
import topology.opens

import .presheaf_stuff.stuff

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
(monotone : Π (x : F.X) (a b : G.to_PresheafedSpace.stalk' (PresheafedSpace.hom.f hom x)),
   (a ≤ b) ↔ ((stalk_map' hom x) a ≤ (stalk_map' hom x) b))
.

-- FIXME can't tag this with @[extensionality]?
lemma hom.ext {F G : C.{v}} {f g : hom F G} (w : f.hom = g.hom) : f = g :=
begin
  cases f, cases g,
  congr; assumption
end

-- We need two lemmas about `stalk_map'`:
section

@[simp] lemma stalk_map'_id (F : PresheafedSpace.{v} TopCommRing.{v}) (x : F.X) :
  stalk_map' (𝟙 F) x = 𝟙 (F.stalk' x) :=
begin
  dsimp [stalk_map', stalk'],
  -- because of tangled type dependencies, we're going to have to give the original proof all over again
  dsimp [stalk_map, whisker_right],
  simp [id_c],
  rw ←category_theory.functor.map_comp,
  rw ←category_theory.functor.map_comp,
  -- convert (stalk_functor C x).map_id F.𝒪,
  -- tidy,
  -- -- Shoot, this is why I wanted to take @[simp] off the eq_to_hom lemmas
  -- conv { to_lhs, congr, skip, rw ←eq_to_hom_map },
  -- rw ←category_theory.functor.map_comp,
  -- rw [eq_to_hom_op_comp],
  -- erw category_theory.functor.map_id,

end
@[simp] lemma stalk_map'_comp {F G H : PresheafedSpace.{v} TopCommRing.{v}} (α : F ⟶ G) (β : G ⟶ H) (x : F.X) :
  stalk_map' (α ≫ β) x =
    begin
      have p := (stalk_map' β (α x) : H.stalk' (β (α x)) ⟶ G.stalk' (α x)),
      have q := (stalk_map' α x : G.stalk' (α x) ⟶ F.stalk' x),
      exact q ∘ p
    end :=
sorry
end

def hom.id (F : C.{v}) : hom F F :=
{ hom := 𝟙 F.to_PresheafedSpace,
  monotone := λ x a b, by simp,  }

def hom.comp (F G H : C.{v}) (α : hom F G) (β : hom G H) : hom F H :=
{ hom := α.hom ≫ β.hom,
  monotone := λ x a b,
  begin
    simp,
    transitivity,
    apply β.monotone,
    apply α.monotone,
  end  }

section
local attribute [simp] id comp
instance : category C.{v} :=
{ hom := hom,
  id := hom.id,
  comp := hom.comp,
  comp_id' := λ X Y f, sorry,
  id_comp' := λ X Y f, sorry,
  assoc' := λ W X Y Z f g h, sorry }
end
