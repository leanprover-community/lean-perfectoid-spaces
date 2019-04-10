import category_theory.limits.limits
import category_theory.limits.types -- So we know that Type has colimits

universes v u

open category_theory
open category_theory.limits

namespace category_theory

variables (C : Type u) [𝒞 : small_category C]
include 𝒞

-- The versions of these that Reid defined just give existential statements,
-- which are harder to work with.
class is_filtered' extends inhabited C :=
(cocone_objs : ∀ (X Y : C), Σ (Z : C), (X ⟶ Z) × (Y ⟶ Z))
(cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), { p : Σ Z, Y ⟶ Z // f ≫ p.2 = g ≫ p.2 })

end category_theory

open category_theory

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞
variables [has_colimits.{v} C]
variables {J : Type v} [small_category J]
variable (F : J ⥤ C)

-- This definition isn't really necessary once you know the syntax for
-- constructing (co)cones. (Usually one would just first package `f` and `w`
-- into a `c : cocone F`, and construct this function by `colimit.desc F c`.)

def desc (F : J ⥤ C) [has_colimit F] (X : C)
  (f : Π j, F.obj j ⟶ X) (w : Π (j j') (k : j ⟶ j'), F.map k ≫ f j' = f j)
  : colimit F ⟶ X :=
colimit.desc F
{ X := X,
  ι :=
  { app := λ j, f j,
    naturality' := λ j j' k, begin dsimp, simp, exact w j j' k end }}

omit 𝒞
variables [is_filtered'.{v} J]

def desc₂ (F : J ⥤ Type v) (X : Type v)
  (f : Π j, F.obj j → F.obj j → X)
  (w : Π (j j') (k : j ⟶ j'), (λ x y, f j' (F.map k x) (F.map k y)) = f j)
  : colimit F ⟶ (colimit F ⟶ X) :=
-- We're trying to construct a function g(-, -).
-- For each fixed value of `x` we construct the function g(x,-):
let g : Π (j) (x : F.obj j), colimit F → X :=
  λ j x,
  colimit.desc F
  { X := X,
    ι :=
    { app := λ j' y, let t₀ := is_filtered'.cocone_objs.{v} j j' in f (t₀.1) (F.map t₀.2.1 x) (F.map t₀.2.2 y),
      naturality' := λ j₁ j₂ k, funext $ λ y,
      begin
        -- Whee, fun with filtered categories:
        dsimp,
        let t₁ := is_filtered'.cocone_objs j j₁,
        let t₂ := is_filtered'.cocone_objs j j₂,
        let t₃ := is_filtered'.cocone_objs t₁.1 t₂.1,
        let t₄ := is_filtered'.cocone_maps (t₁.2.1 ≫ t₃.2.1) (t₂.2.1 ≫ t₃.2.2),
        let t₅ := is_filtered'.cocone_maps (t₁.2.2 ≫ t₃.2.1 ≫ t₄.1.2) (k ≫ t₂.2.2 ≫ t₃.2.2 ≫ t₄.1.2),
        rw ←(w t₁.1 t₅.1.1 (t₃.2.1 ≫ t₄.1.2 ≫ t₅.1.2)),
        rw ←(w t₂.1 t₅.1.1 (t₃.2.2 ≫ t₄.1.2 ≫ t₅.1.2)),
        dsimp,
        congr; repeat { rw ←functor_to_types.map_comp },
        { have p := congr_arg (λ x, x ≫ t₅.1.2) t₄.2,
          dsimp at p,
          repeat { rw category.assoc at p },
          rw p, },
        { have p := t₅.2,
          repeat { rw category.assoc at p },
          rw p, },
      end } }
in
colimit.desc F
  { X := colimit F → X,
    ι :=
    { app := λ j x, g j x,
      naturality' := λ j₁ j₂ k, funext $ λ x,
      begin
        dsimp [g], clear g,
        ext h,
        induction h,
        cases h with j' y,
        dsimp,
        -- Almost the same fun!
        let t₁ := is_filtered'.cocone_objs j₁ j',
        let t₂ := is_filtered'.cocone_objs j₂ j',
        let t₃ := is_filtered'.cocone_objs t₁.1 t₂.1,
        let t₄ := is_filtered'.cocone_maps (t₁.2.1 ≫ t₃.2.1) (k ≫ t₂.2.1 ≫ t₃.2.2),
        let t₅ := is_filtered'.cocone_maps (t₁.2.2 ≫ t₃.2.1 ≫ t₄.1.2) (t₂.2.2 ≫ t₃.2.2 ≫ t₄.1.2),
        rw ←(w t₁.1 t₅.1.1 (t₃.2.1 ≫ t₄.1.2 ≫ t₅.1.2)),
        rw ←(w t₂.1 t₅.1.1 (t₃.2.2 ≫ t₄.1.2 ≫ t₅.1.2)),
        dsimp,
        congr; repeat { rw ←functor_to_types.map_comp },
        { have p := congr_arg (λ x, x ≫ t₅.1.2) t₄.2,
          dsimp at p,
          repeat { rw category.assoc at p },
          rw p, },
        { have p := t₅.2,
          repeat { rw category.assoc at p },
          rw p, },
        refl,
      end }}
