import topology.algebra.ring

import ring_theory.subring
import ring_theory.ideal_operations
import for_mathlib.nonarchimedean.open_subgroup

universes u v

variables {A : Type u} {B : Type v}
variables [comm_ring A] [topological_space A] [topological_ring A]
variables [comm_ring B] [topological_space B] [topological_ring B]

open set topological_ring

instance subring_has_zero (R : Type u) [comm_ring R] (S : set R) [HS : is_subring S] : has_zero S :=
⟨⟨0, is_add_submonoid.zero_mem S⟩⟩

instance topological_subring (A₀ : set A) [is_subring A₀] : topological_ring A₀ :=
{ continuous_neg := continuous_subtype_mk _ $ (continuous_neg A).comp continuous_subtype_val,
  continuous_add := continuous_subtype_mk _ $ continuous_add
    (continuous_subtype_val.comp continuous_fst)
    ( continuous_subtype_val.comp continuous_snd),
  continuous_mul := continuous_subtype_mk _ $ continuous_mul
    (continuous_subtype_val.comp continuous_fst)
    (continuous_subtype_val.comp continuous_snd) }

lemma half_nhds {s : set A} (hs : s ∈ (nhds (0 : A))) :
  ∃ V ∈ (nhds (0 : A)), ∀ v w ∈ V, v * w ∈ s :=
begin
  have : ((λa:A×A, a.1 * a.2) ⁻¹' s) ∈ (nhds ((0, 0) : A × A)) :=
    tendsto_mul' (by simpa using hs),
  rw nhds_prod_eq at this,
  rcases filter.mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, filter.inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

-- lemma continuous_mul_left (a : A) : continuous (λ x, a * x) :=
-- continuous_mul continuous_const continuous_id
-- 
-- lemma continuous_mul_right (a : A) : continuous (λ x, x * a) :=
-- continuous_mul continuous_id continuous_const

lemma is_open_ideal_map_open_embedding {f : A → B} [is_ring_hom f]
  (emb : embedding f) (hf : is_open (range f)) (I : ideal A) (hI : is_open (↑I : set A)) :
  is_open (↑(I.map f) : set B) :=
begin
  apply @open_add_subgroup.is_open_of_open_add_subgroup _ _ _ _ _,
  { exact submodule.submodule_is_add_subgroup _ },
  { refine ⟨⟨f '' I, embedding_open emb hf hI, by apply_instance⟩, ideal.subset_span⟩,
    apply_instance }
end

instance pi_topological_ring {I : Type*} {R : I → Type*} [∀ i, comm_ring (R i)] [∀ i, topological_space (R i)]
  [h : ∀ i, topological_ring (R i)] : topological_ring (Π (i : I), R i) :=
{ continuous_add := continuous_pi₂ (λ i, (h i).continuous_add),
  continuous_mul := continuous_pi₂ (λ i, (h i).continuous_mul),
  continuous_neg := continuous_pi₁ (λ i, (h i).continuous_neg) }

section
open filter

class ring_with_zero_nhd (α : Type u) extends ring α:=
(Z : filter α)
(zero_Z {} : pure 0 ≤ Z)
(sub_Z {} : tendsto (λp:α×α, p.1 - p.2) (Z.prod Z) Z)
(left_mul (x₀ : α) : tendsto (λ x : α, x₀ * x) Z Z)
(right_mul (x₀ : α) : tendsto (λ x : α, x * x₀) Z Z)
(mul_Z {} : tendsto (λp:α×α, p.1 * p.2) (Z.prod Z) Z)

end

namespace ring_with_zero_nhd
variables (α : Type*) [ring_with_zero_nhd α]
open filter add_group_with_zero_nhd function
local notation `Z` := add_group_with_zero_nhd.Z

def to_add_group_with_zero_nhd {α :Type*} [ring_with_zero_nhd α] :
  add_group_with_zero_nhd α :=
{..‹ring_with_zero_nhd α›}

local attribute [instance] to_add_group_with_zero_nhd

def topological_space : topological_space α := by apply_instance

def is_topological_ring : topological_ring α :=
begin
  refine {..add_group_with_zero_nhd.topological_add_group, ..},
  rw continuous_iff_continuous_at,
  rintro ⟨x₀, y₀⟩,
  rw [continuous_at, nhds_prod_eq, nhds_eq', nhds_eq', nhds_eq', filter.prod_map_map_eq,
      tendsto_map'_iff],
  suffices :
  tendsto ((λ (x : α), x + x₀ * y₀) ∘ (λ (p : α × α), p.fst + p.snd) ∘
            (λ (p : α × α), (p.1*y₀ + x₀*p.2, p.1*p.2)))
    (filter.prod (Z α) $ Z α)
    (map (λ (x : α), x + x₀ * y₀) $ Z α),
  { convert this using 1,
    { ext, simp only [comp_app],
      repeat { rw mul_add <|> rw add_mul },
      abel },
    simp },
  refine tendsto.comp tendsto_map _,
  refine tendsto.comp add_Z _,
  apply tendsto.prod_mk _ ring_with_zero_nhd.mul_Z,
  { change tendsto ((λ p : α × α, p.1 + p.2) ∘ (λ (x : α × α), (x.fst * y₀, x₀ * x.snd))) (filter.prod (Z α) (Z α)) (Z α),
    refine tendsto.comp add_Z _,
    apply tendsto.prod_mk,
    { exact (ring_with_zero_nhd.right_mul y₀).comp  tendsto_fst},
    { exact (ring_with_zero_nhd.left_mul  x₀).comp  tendsto_snd} },
end

end ring_with_zero_nhd
