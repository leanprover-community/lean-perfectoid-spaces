/-
This file is devoted to a lemma that I think is the correct one in order to prove that completions
of sufficiently nice topological fields are topological fields.

In the intended application, φ is the inversion x ↦ x⁻¹ on K^*, to be extended to \hat{K} ∖ {0}
-/
import topology.uniform_space.uniform_embedding

open set filter

local notation `𝓝` := nhds

def cauchy_of {α : Type*} {β : Type*} [U : uniform_space β] (f : α → β) (F : filter α) :=
@cauchy α (uniform_space.comap f U) F

/-
       i_X       φ       i_R
    X ←———— X' ————→ R' ————⟶ R
    |       |        |        |
j_X |    k_X|        |k_R     | j_R
    ↓       ↓        ↓        ↓
    Y ←———— Y' - - → S' ————⟶ S
       i_Y       ψ       i_S
-/

lemma continuous_extend_of_really_wants_to
  {X : Type*} {Y : Type*} {R : Type*} {S : Type*}
  {X' : Type*} {Y' : Type*} {R' : Type*} {S' : Type*}
  [uniform_space X] [uniform_space Y] [uniform_space R] [uniform_space S]
  [topological_space X'] [topological_space Y'] [topological_space R'] [topological_space S']
  {i_X : X' → X} {j_X : X → Y} {k_X : X' → Y'} {i_Y : Y' → Y}
  {i_R : R' → R} {j_R : R → S} {k_R : R' → S'} {i_S : S' → S} (φ : X' → R')
  (commX : i_Y ∘ k_X = j_X ∘ i_X) (commR : i_S ∘ k_R = j_R ∘ i_R)
  (hiX : dense_embedding i_X) (hkX : dense_embedding k_X) (hiY : dense_embedding i_Y)
  (hiR : dense_embedding i_R) (hkR : dense_embedding k_R) (hiS : dense_embedding i_S)
  (hjX : uniform_embedding j_X) (hjR : uniform_embedding j_R)
  (hX : j_X ⁻¹' range i_Y ⊆ range i_X) (hR : -range i_S ⊆ j_R '' -range i_R)
  (hφ : ∀ F : filter X', cauchy_of i_X F → (∀ x ∉ range i_X, (comap i_X $ 𝓝 x) ⊓ F = ⊥) →
           (cauchy_of i_R $ map φ F) ∧ ∀ r ∉ range i_R, (comap i_R $ 𝓝 r) ⊓ map φ F = ⊥) :
  continuous (hkX.extend $ k_R ∘ φ) :=
sorry
