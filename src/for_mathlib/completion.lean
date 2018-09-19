/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

Hausdorff completions of uniform spaces.

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `completion α` and a morphism
(ie. uniformly continuous map) `to_completion : α → completion α` which solves the universal
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`.
It means any uniformly continuous `f : α → β` gives rise to a unique morphism
`completion.map f : completion α → β` such that `f = completion_extension f ∘ to_completion α`.
Actually `completion_extension f` is defined for all maps from `α` to `β` but it has the desired
properties only if `f` is uniformly continuous.

Beware that `to_completion α` is not injective if `α` is not Hausdorff. But its image is always
dense.

The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, if turns `f : α → β` into
a morphism `completion.map f : completion α → completion β` such that
`(to_completion β) ∘ f = (completion.map f) ∘ to_completion α` provided `f` is uniformly continuous.
This construction is compatible with composition.

This formalization is mostly based on N. Bourbaki: /General Topology/ but from a slightly
different perspective in order to reuse material in analysis.topology.uniform_space.
-/

import analysis.topology.uniform_space
import analysis.topology.continuity
import data.set.function

import for_mathlib.uniform_space
import for_mathlib.data.set.basic

local attribute [instance, priority 0] classical.prop_decidable

local attribute [instance] separation_setoid

open Cauchy set

namespace uniform_space
variables (α : Type*) [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]

/-- Hausdorff completion of `α` -/
def completion := quotient (separation_setoid $ Cauchy α)

@[priority 50]
instance completion_uniform_space : uniform_space (completion α) := by unfold completion ; apply_instance

instance completion_complete : complete_space (completion α) := complete_space_separation

instance completion_separated : separated (completion α) := separated_separation

instance completion_t2 : t2_space (completion α) := separated_t2

instance completion_regular : regular_space (completion α) := separated_regular

/-- Canonical map. Not always injective. -/
def to_completion : α → completion α := quotient.mk ∘ pure_cauchy

/-- Automatic coercion from `α` to its completion -/
instance : has_coe α (completion α) := ⟨to_completion α⟩

@[simp]
lemma completion_coe : ∀ a : α, to_completion α a = (a : completion α) := assume a, rfl

namespace to_completion
open set

lemma uniform_continuous : uniform_continuous (to_completion α) :=
uniform_continuous.comp uniform_embedding_pure_cauchy.uniform_continuous
  uniform_continuous_quotient_mk

lemma continuous : continuous (to_completion α) :=
uniform_continuous.continuous (uniform_continuous α)

variable {α}

lemma dense : closure (range (to_completion α)) = univ   :=
begin
  dsimp[to_completion],
  rw range_comp,
  exact quotient_dense_of_dense pure_cauchy_dense
end

lemma dense₁ : closure (range (λ x : α, (x : completion α))) = univ :=
to_completion.dense

lemma dense₂ : let φ : α × β → (completion α) × (completion β) := λ x, ⟨x.1, x.2⟩ in
  closure (range φ) = univ :=
begin
  intro φ,
  have : range φ = set.prod (range (to_completion α)) (range (to_completion β)),
  { ext x,
    dsimp[φ],
    unfold_coes,
    simp[prod.ext_iff] },
  simp [this, closure_prod_eq, dense]
end

lemma dense₃ : let β := completion α in let φ : α × α × α → β × β × β := λ x, ⟨x.1, x.2.1, x.2.2⟩ in
  closure (range φ) = univ :=
begin
  intros β φ,
  have : range φ = set.prod (range (to_completion α))
    (set.prod (range (to_completion α)) (range (to_completion α))),
  { ext x,
    dsimp[φ],
    unfold_coes,
    simp[prod.ext_iff] },
  simp [this, closure_prod_eq, dense]
end

lemma uniform_embedding [separated α] : uniform_embedding (coe : α → completion α) :=
⟨injective_separated_pure_cauchy,
  begin
   change filter.comap ((λ (y : Cauchy α × Cauchy α), (⟦y.1⟧, ⟦y.2⟧)) ∘
     (λ (x : α × α), (pure_cauchy x.1, pure_cauchy x.2))) uniformity = uniformity,
   rw [←filter.comap_comap_comp, comap_quotient_eq_uniformity, uniform_embedding_pure_cauchy.2]
  end⟩
end to_completion

variable {α}
lemma nonempty_completion_iff : nonempty (completion α) ↔ nonempty α :=
begin
  split ; rintro ⟨c⟩,
  { have := eq_univ_iff_forall.1 to_completion.dense c,
    have := mem_closure_iff.1 this _ is_open_univ trivial,
    rcases exists_mem_of_ne_empty this with ⟨_, ⟨_, a, _⟩⟩,
    exact ⟨a⟩ },
  { exact ⟨to_completion α c⟩ }
end

variables [complete_space β] [separated β]

/-- "Extension" to the completion.
    Defined for any map `f` but returns garbage if `f` is not uniformly continuous -/
noncomputable
def completion_extension (f : α → β) : completion α → β :=
if H : uniform_continuous f then
  let g₀ := (uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense).extend f in
  have g₀_unif : uniform_continuous g₀ :=
    uniform_continuous_uniformly_extend uniform_embedding_pure_cauchy pure_cauchy_dense H,
  have compat : ∀ p q : Cauchy α, p ≈ q → g₀ p = g₀ q :=
    assume p q h, eq_of_separated_of_uniform_continuous g₀_unif h,
  quotient.lift g₀ compat
else
  λ x, f (classical.inhabited_of_nonempty $ nonempty_completion_iff.1 ⟨x⟩).default

/-- Completion functor acting on morphisms -/
noncomputable def completion.map (f : α → γ) : completion α → completion γ :=
completion_extension ((to_completion γ) ∘ f)
end uniform_space

namespace completion_extension
open uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables [complete_space β] [separated β]

variables {f : α → β} (H : uniform_continuous f)
include H

lemma lifts : f = (completion_extension f) ∘ to_completion α :=
begin
  unfold completion_extension,
  simp [H],
  ext x,
  let lim := H.continuous.tendsto x,
  have := (uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense).extend_e_eq lim,
  rw ←this,
  refl
end

@[simp]
lemma lifts' : ∀ a : α, f a = (completion_extension f) a := λ a, congr_fun (lifts H) a

lemma uniform_continuity : uniform_continuous (completion_extension f) :=
begin
  unfold completion_extension,
  split_ifs,
  let g := completion_extension f,
  intros r r_in,
  let g₀ := (uniform_embedding_pure_cauchy.dense_embedding pure_cauchy_dense).extend f,
  have g₀_unif : uniform_continuous g₀ :=
    uniform_continuous_uniformly_extend uniform_embedding_pure_cauchy pure_cauchy_dense H,

  rw filter.mem_map,
  dsimp[completion],
  rw prod_quotient_preimage_eq_image _ rfl r,
  exact filter.image_mem_map (g₀_unif r_in)
end

lemma continuity : continuous (completion_extension f) :=
uniform_continuous.continuous (uniform_continuity H)

lemma unique {h : completion α → β} :
  uniform_continuous h → f = (h ∘ to_completion α) → h = completion_extension f :=
begin
  let g := completion_extension f,
  have g_unif : uniform_continuous g := uniform_continuity H,
  intros h_unif h_lifts,
  change h = g,
  ext x,
  have closed_eq : is_closed {x | h x = g x} := is_closed_eq h_unif.continuous g_unif.continuous,
  have : f = g ∘ to_completion α := lifts H,
  have eq_on_α : ∀ x, (h ∘ to_completion α) x = (g ∘ to_completion α) x, by cc,
  exact (is_closed_property to_completion.dense closed_eq eq_on_α x : _)
end
end completion_extension

namespace completion
variables {α : Type*} [uniform_space α] {β : Type*} [uniform_space β]
open uniform_space uniform_space.pure_cauchy


noncomputable
def prod : (completion α) × (completion β) → completion (α × β) :=
begin
  let g₀ := λ (a : Cauchy α) (b : Cauchy β),  (prod.de.extend (to_completion (α × β))) (a, b),

  refine function.uncurry (quotient.lift₂ g₀ _),
  { intros a₁ b₁ a₂ b₂ eqv₁ eqv₂,
    have g₁_uc : uniform_continuous (prod.de.extend (to_completion (α × β))),
    { let ue : uniform_embedding (λ (p : α × β), (pure_cauchy (p.fst), pure_cauchy (p.snd))) :=
        uniform_embedding.prod uniform_embedding_pure_cauchy uniform_embedding_pure_cauchy,
      refine uniform_continuous_uniformly_extend ue _ (to_completion.uniform_continuous (α × β)) },

    exact (eq_of_separated_of_uniform_continuous g₁_uc (separation_prod.2 ⟨eqv₁, eqv₂⟩) : _) },
end

lemma prod.uc : uniform_continuous (@prod α _ β _) :=
begin
  dsimp[prod],
  rw function.uncurry_def,
  apply uniform_continuous_quotient_lift₂,
  suffices : uniform_continuous (dense_embedding.extend prod.de (to_completion (α × β))),
  by simpa,
  exact uniform_continuous_uniformly_extend
    (uniform_embedding.prod uniform_embedding_pure_cauchy uniform_embedding_pure_cauchy)
    prod.de.dense (to_completion.uniform_continuous _)
end

@[simp]
lemma prod.lifts (a : α) (b : β) : @prod α _ β _ (a, b) = (a, b) :=
begin
  let f := to_completion (α × β),
  change dense_embedding.extend prod.de f (pure_cauchy a, pure_cauchy b) = ⟦pure_cauchy (a, b)⟧,

  have hf : filter.tendsto f (nhds (a, b)) (nhds (f (a,b))) :=
    continuous.tendsto (to_completion.continuous _) _,

  exact (prod.de.extend_e_eq hf : _)
end
/-- Canonical map completion (α × β) → (completion α) × (completion β). Not used in group_completion. -/
noncomputable def prod_inv : completion (α × β) → (completion α) × (completion β) :=
completion_extension (λ x, (x.1, x.2))

@[simp]
lemma prod_inv.lifts : ∀ x : α × β, prod_inv (x : completion (α × β)) = ((x.1 : completion α), (x.2 : completion β)) :=
begin
  intros x,
  have u1 := uniform_continuous.comp uniform_continuous_fst (to_completion.uniform_continuous α),
  have u2 := uniform_continuous.comp uniform_continuous_snd (to_completion.uniform_continuous β),
  have := completion_extension.lifts' (uniform_continuous.prod_mk u1 u2) x,
  simp at this,
  unfold_coes,
  simpa [this]
end

lemma prod_inv.uc : uniform_continuous (@prod_inv α _ β _) :=
begin
  have u1 := uniform_continuous.comp uniform_continuous_fst (to_completion.uniform_continuous α),
  have u2 := uniform_continuous.comp uniform_continuous_snd (to_completion.uniform_continuous β),
  exact completion_extension.uniform_continuity (uniform_continuous.prod_mk u1 u2)
end
end completion

namespace uniform_space
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]
open uniform_space function

noncomputable def completion.map₂ (f : α → β → γ) : completion α × completion β → completion γ :=
  completion.map (uncurry f) ∘ completion.prod
end uniform_space

namespace completion.map
open uniform_space uniform_space.completion
variables {α : Type*} [uniform_space α]
variables {β : Type*} [uniform_space β]
variables {γ : Type*} [uniform_space γ]
variables {δ : Type*} [uniform_space δ]

variables {f : α → β} (H : uniform_continuous f)
variables {g : β → γ} (H' : uniform_continuous g)

lemma lifts : (to_completion β) ∘ f = (map f) ∘ to_completion α :=
completion_extension.lifts $ uniform_continuous.comp H (to_completion.uniform_continuous β)

lemma lifts' : ∀ a : α, (f a : completion β) = map f a :=
congr_fun (lifts H)

lemma unique {f' : completion α → completion β} :
  uniform_continuous f' → (to_completion β) ∘ f = f' ∘ to_completion α → f' = map f :=
completion_extension.unique $ uniform_continuous.comp H (to_completion.uniform_continuous β)

lemma uniform_continuity : uniform_continuous (map f) :=
completion_extension.uniform_continuity $ uniform_continuous.comp H (to_completion.uniform_continuous β)

protected lemma id : map (@id α) = id :=
by rw (unique uniform_continuous_id uniform_continuous_id) ; simp

@[simp]
protected lemma const (a : α) : map (λ x : α, a) = (λ x, a) :=
by rw unique uniform_continuous_const uniform_continuous_const ; refl

lemma prod_prod_inv : completion.prod ∘ (@completion.prod_inv α _ β _) = id :=
begin
  rw ←completion.map.id,
  apply completion.map.unique uniform_continuous_id
    (uniform_continuous.comp completion.prod_inv.uc completion.prod.uc),
  ext x,
  simp
end

lemma prod_inv_prod : completion.prod_inv ∘ (@completion.prod α _ β _) = id :=
begin
  funext x,
  have closed : is_closed {x | (completion.prod_inv ∘ (@completion.prod α _ β _)) x = id x},
  { have c₁ : continuous (completion.prod_inv ∘ (@completion.prod α _ β _)) :=
      continuous.comp (completion.prod.uc.continuous) (completion.prod_inv.uc.continuous),
    exact is_closed_eq c₁ continuous_id },

  exact (is_closed_property to_completion.dense₂ closed (by simp) x : _)
end

include H H'
lemma comp : map (g ∘ f) = (map g) ∘ map f :=
begin
  let l  := completion.map f,
  let l' := completion.map g,
  have : uniform_continuous (g ∘ f) := uniform_continuous.comp H H',
  have : uniform_continuous (l' ∘ l ):=
    uniform_continuous.comp (uniform_continuity H) (uniform_continuity H'),
  have : (to_completion γ ∘ g) ∘ f = (l' ∘ l) ∘ to_completion α := calc
    (to_completion γ ∘ g) ∘ f = (l' ∘ to_completion β) ∘ f : by rw completion.map.lifts H'
    ... = l' ∘ (to_completion β ∘ f) : rfl
    ... = l' ∘ (l  ∘ to_completion α) : by rw completion.map.lifts H,
  apply eq.symm,
  apply unique ; assumption
end
omit H H'

open function
variables {h : α → β → γ} (h_uc : uniform_continuous (uncurry h))

include h_uc
lemma lifts₂ : (to_completion γ) ∘ (uncurry h) = (map₂ h) ∘ (λ p, (p.1, p.2)) :=
begin
  ext x,
  rw lifts h_uc,
  apply congr_arg (map (uncurry h)),
  simp
end

lemma lifts₂' : ∀ (a : α) (b : β), (h a b : completion γ) = map₂ h (a, b) :=
λ a b, congr_fun (lifts₂ h_uc) (a,b)

lemma uniform_continuity₂ : uniform_continuous (map₂ h) :=
uniform_continuous.comp completion.prod.uc (uniform_continuity h_uc)

lemma map₂_map_map {f : δ → α} {g : δ → β} (f_uc : uniform_continuous f) (g_uc : uniform_continuous g) :
  map (λ x, h (f x) (g x)) = λ y, map₂ h (map f y, map g y) :=
begin
  apply eq.symm,
  have uc₁ := (uniform_continuous.comp (uniform_continuous.prod_mk f_uc g_uc) h_uc),
  have uc₂ := (uniform_continuous.comp (uniform_continuous.prod_mk (uniform_continuity f_uc) (uniform_continuity g_uc)) (uniform_continuity₂ h_uc)),
  apply unique uc₁ uc₂,
  ext x,
  change (h (f x) (g x) : completion γ) = map₂ h (map f x, map g x),
  rw [←lifts' f_uc x, ←lifts' g_uc x, lifts₂' h_uc]
end
end completion.map