/-
  Continuous maps and presheaves.

  https://stacks.math.columbia.edu/tag/008C

  Author: Ramon Fernandez Mir
-/

import for_mathlib.sheaves.opens
import for_mathlib.sheaves.presheaf

universes u v w

open topological_space

variables {α : Type u} [topological_space α]
variables {β : Type v} [topological_space β]
variables {f : α → β} (Hf : continuous f)

-- f induces a functor PSh(α) ⟶ PSh(β).

namespace presheaf

section pushforward

def pushforward (F : presheaf α) : presheaf β :=
{ F := λ U, F (opens.comap Hf U),
  res := λ U V HVU, F.res (opens.comap Hf U) (opens.comap Hf V) (opens.comap_mono Hf V U HVU),
  Hid := λ U, F.Hid (opens.comap Hf U),
  Hcomp := λ U V W HWV HVU,
    F.Hcomp (opens.comap Hf U) (opens.comap Hf V) (opens.comap Hf W)
            (opens.comap_mono Hf W V HWV) (opens.comap_mono Hf V U HVU), }

def pushforward.morphism (F G : presheaf α) (φ : F ⟶ G)
: pushforward Hf F ⟶ pushforward Hf G :=
{ map := λ U, φ.map (opens.comap Hf U),
  commutes := λ U V HVU,
    φ.commutes (opens.comap Hf U) (opens.comap Hf V) (opens.comap_mono Hf V U HVU), }

end pushforward

-- f induces a functor PSh(β) ⟶ PSh(α). Simplified to the case when f is open.

section pullback

variable (Hf' : ∀ (U : opens α), is_open (f '' U))

def pullback (F : presheaf β) : presheaf α :=
{ F := λ U, F (opens.map Hf' U),
  res := λ U V HVU, F.res (opens.map Hf' U) (opens.map Hf' V) (opens.map_mono Hf' V U HVU),
  Hid := λ U, F.Hid (opens.map Hf' U),
  Hcomp := λ U V W HWV HVU,
    F.Hcomp (opens.map Hf' U) (opens.map Hf' V) (opens.map Hf' W)
            (opens.map_mono Hf' W V HWV) (opens.map_mono Hf' V U HVU), }

def pullback.morphism (F G : presheaf β) (φ : F ⟶ G) : pullback Hf' F ⟶ pullback Hf' G :=
{ map := λ U, φ.map (opens.map Hf' U),
  commutes := λ U V HVU,
    φ.commutes (opens.map Hf' U) (opens.map Hf' V) (opens.map_mono Hf' V U HVU), }

end pullback

-- f induces a `map` from a presheaf on β to a presheaf on α.

structure fmap (F : presheaf α) (G : presheaf β) :=
(map      : ∀ (U), G U → F (opens.comap Hf U))
(commutes : ∀ (U V) (HVU : V ⊆ U),
  (map V) ∘ (G.res U V HVU)
= (F.res (opens.comap Hf U) (opens.comap Hf V) (opens.comap_mono Hf V U HVU)) ∘ (map U))

namespace fmap

variables {γ : Type w} [topological_space γ]
variables {g : β → γ} {Hg : continuous g}

variable {Hf}

def comp {F : presheaf α} {G : presheaf β} {H : presheaf γ}
(f_ : fmap Hf F G) (g_ : fmap Hg G H) : fmap (Hg.comp Hf) F H :=
{ map := λ U, (f_.map (opens.comap Hg U)) ∘ (g_.map U),
  commutes := λ U V HVU,
    by { rw [function.comp.assoc _ _ (H.res _ _ _),  g_.commutes,
             ←function.comp.assoc _ _ (g_.map _), f_.commutes],
         refl } }

def id (F : presheaf α) : fmap continuous_id F F :=
{ map := λ U,
    begin
      have HUU : opens.comap continuous_id U ⊆ U,
        intros x Hx,
        dsimp [opens.comap] at Hx,
        exact Hx,
      exact (F.res U (opens.comap continuous_id U) HUU),
    end,
  commutes := λ U V HUV, by iterate 2 { rw ←F.Hcomp } }
end fmap

end presheaf
