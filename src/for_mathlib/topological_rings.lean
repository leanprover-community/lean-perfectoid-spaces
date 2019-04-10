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
{ continuous_neg := continuous_subtype_mk _ $ continuous_subtype_val.comp $ continuous_neg A,
  continuous_add := continuous_subtype_mk _ $ continuous_add
    (continuous_fst.comp continuous_subtype_val)
    (continuous_snd.comp continuous_subtype_val),
  continuous_mul := continuous_subtype_mk _ $ continuous_mul
    (continuous_fst.comp continuous_subtype_val)
    (continuous_snd.comp continuous_subtype_val) }

lemma half_nhds {s : set A} (hs : s ∈ (nhds (0 : A))) :
  ∃ V ∈ (nhds (0 : A)), ∀ v w ∈ V, v * w ∈ s :=
begin
  have : ((λa:A×A, a.1 * a.2) ⁻¹' s) ∈ (nhds ((0, 0) : A × A)) :=
    tendsto_mul' (by simpa using hs),
  rw nhds_prod_eq at this,
  rcases filter.mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, filter.inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

lemma continuous_mul_left (a : A) : continuous (λ x, a * x) :=
continuous_mul continuous_const continuous_id

lemma continuous_mul_right (a : A) : continuous (λ x, x * a) :=
continuous_mul continuous_id continuous_const

lemma is_open_ideal_map_open_embedding {f : A → B} [is_ring_hom f]
  (emb : embedding f) (hf : is_open (range f)) (I : ideal A) (hI : is_open (↑I : set A)) :
  is_open (↑(I.map f) : set B) :=
begin
  apply @open_add_subgroup.is_open_of_open_add_subgroup _ _ _ _ _,
  { exact submodule.submodule_is_add_subgroup _ },
  { refine ⟨⟨f '' I, embedding_open emb hf hI, by apply_instance⟩, ideal.subset_span⟩,
    apply_instance }
end
