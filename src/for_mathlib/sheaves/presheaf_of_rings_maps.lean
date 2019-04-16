/-
  Continuous maps and presheaves of rings.

  https://stacks.math.columbia.edu/tag/008C

  Author: Ramon Fernandez Mir
-/

import for_mathlib.sheaves.opens
import for_mathlib.sheaves.presheaf_of_rings
import for_mathlib.sheaves.presheaf_maps

universes u v w

open topological_space

variables {α : Type u} [topological_space α]
variables {β : Type v} [topological_space β]

namespace presheaf_of_rings

-- f induces a functor PSh(α) ⟶ PSh(β).

section pushforward

variables {f : α → β} (Hf : continuous f)

def pushforward (F : presheaf_of_rings α) : presheaf_of_rings β :=
{ Fring := λ U, F.Fring _,
  res_is_ring_hom := λ U V HVU, F.res_is_ring_hom _ _ _,
  ..presheaf.pushforward Hf F.to_presheaf }

def pushforward.morphism (F G : presheaf_of_rings α) (φ : F ⟶ G)
: pushforward Hf F ⟶ pushforward Hf G :=
{ ring_homs := λ U, φ.ring_homs _,
  ..presheaf.pushforward.morphism Hf F.to_presheaf G.to_presheaf φ.to_morphism }

end pushforward

-- f induces a functor PSh(β) ⟶ PSh(α). Simplified to the case when f is 'nice'.

section pullback

variable (α)

structure pullback (F : presheaf_of_rings β) :=
(φ       : α → β)
-- Open immersion. TODO: Package this.
(Hφ₁     : continuous φ)
(Hφ₂     : ∀ (U : opens α), is_open (φ '' U))
(Hφ₃     : function.injective φ)
(range   : opens β := ⟨φ '' set.univ, Hφ₂ opens.univ⟩)
(carrier : presheaf_of_rings α :=
  { Fring := λ U, F.Fring _,
    res_is_ring_hom := λ U V HVU, F.res_is_ring_hom _ _ _,
    ..presheaf.pullback Hφ₂ F.to_presheaf })

def pullback_id (F : presheaf_of_rings β) : presheaf_of_rings.pullback β F :=
begin
  exact
    { φ := (id : β → β),
      Hφ₁ := continuous_id,
      Hφ₂ := λ U, by rw set.image_id; by exact U.2,
      Hφ₃ := function.injective_id },
  exact F,
end

-- TODO : Quite ugly.
lemma pullback_id.iso (F : presheaf_of_rings β) : (pullback_id F).carrier ≅ F :=
nonempty.intro
{ mor :=
    { map :=
      begin
        intros U,
        have HUU : U ⊆ opens.map (pullback_id F).Hφ₂ U,
          intros x Hx,
          dsimp [opens.map],
          erw set.image_id,
          exact Hx,
        exact F.res (opens.map (pullback_id F).Hφ₂ U) U HUU,
      end,
    commutes :=
      begin
        intros U V HVU,
        dsimp [pullback_id],
        rw ←presheaf.Hcomp,
        rw ←presheaf.Hcomp,
      end,
    ring_homs := by apply_instance, },
  inv :=
    { map :=
        begin
          intros U,
          have HUU : opens.map (pullback_id F).Hφ₂ U ⊆ U,
            intros x Hx,
            dsimp [opens.map] at Hx,
            erw set.image_id at Hx,
            exact Hx,
          exact F.res U (opens.map (pullback_id F).Hφ₂ U) HUU,
        end,
      commutes :=
        begin
          intros U V HVU,
          dsimp [pullback_id],
          rw ←presheaf.Hcomp,
          rw ←presheaf.Hcomp,
        end,
      ring_homs := by apply_instance, },
  mor_inv_id :=
    begin
      simp [presheaf.comp],
      congr,
      funext U,
      rw ←presheaf.Hcomp,
      erw presheaf.Hid,
    end,
  inv_mor_id :=
    begin
      simp [presheaf.comp],
      congr,
      funext U,
      rw ←presheaf.Hcomp,
      erw presheaf.Hid,
    end, }

end pullback

-- f induces a `map` from a presheaf of rings on β to a presheaf of rings on α.

variable {α}

variables {f : α → β} (Hf : continuous f)

def fmap (F : presheaf_of_rings α) (G : presheaf_of_rings β) :=
presheaf.fmap Hf F.to_presheaf G.to_presheaf

namespace fmap

variables {γ : Type w} [topological_space γ]
variables {g : β → γ} {Hg : continuous g}

variable {Hf}

def comp {F : presheaf_of_rings α} {G : presheaf_of_rings β} {H : presheaf_of_rings γ}
(f_ : fmap Hf F G) (g_ : fmap Hg G H) : fmap (continuous.comp Hf Hg) F H :=
presheaf.fmap.comp f_ g_

end fmap

end presheaf_of_rings
