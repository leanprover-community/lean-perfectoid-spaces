import .bilinear_function_on_stalk
import algebraic_geometry.stalks
import algebraic_geometry.presheaf_of_functions

noncomputable theory

universes v u

open category_theory
open category_theory.instances
open algebraic_geometry
open algebraic_geometry.presheaf_on_space
open topological_space
open topological_space.open_nhds

variables (X : Top.{0})

-- The presheaf of continuous functions X → ℝ (forgetting the ring structure).
def F : presheaf_on_space (Type 0) X := presheaf_of_real_functions X ⋙ CommRing.forget

-- Yuck, why do we have to do this?
instance foo : has_le ((TopCommRing.forget_to_Top.obj TopCommRing.real).α) :=
begin
  show has_le ℝ,
  apply_instance,
end

-- We define a predicate on germs of functions around x, saying f(x)^2 ≤ g(x):
def f2_le_g_at_x (x : X) : (F X).stalk x → (F X).stalk x → Prop :=
stalk_desc₂ X (F X) Prop x
  (λ U f g, (f.1 ⟨x, (unop U).2⟩ : ℝ)^2 ≤ g.1 ⟨x, (unop U).2⟩) -- We need ⟨x, (unop U).2⟩ because we can't feed `x` to `f` until we know it's in the open_nhd.
  (λ U U' i, rfl)
