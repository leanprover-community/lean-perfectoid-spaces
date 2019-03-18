import topology.algebra.ring
import ring_theory.subring

import for_mathlib.adic_topology
import for_mathlib.top_ring
import for_mathlib.topological_rings

open set

/--A commutative topological ring is non-archimedean if every open subset
   containing 0 also contains an open additive subgroup.-/
definition nonarchimedean (G : Type*)
  [add_group G] [topological_space G] [topological_add_group G] : Prop :=
∀ U ∈ nhds (0 : G), ∃ V : set G, is_add_subgroup V ∧ is_open V ∧ V ⊆ U

namespace of_subgroups
variables {A : Type*} [ring A] {ι : Type*} [inhabited ι] (G : ι → set A) [∀ i, is_add_subgroup $ G i]
  (h_directed : ∀ i j, ∃ k, G k ⊆ G i ∩ G j)
  (h_left_mul : ∀ x i, ∃ j, (λ y : A, x*y) '' (G j) ⊆ G i)
  (h_right_mul : ∀ x i, ∃ j, (λ y : A, y*x) '' (G j) ⊆ G i)
  (h_mul : ∀ i, ∃ j, (λ x : A × A, x.1*x.2) '' (set.prod (G j) (G j)) ⊆ G i)
include h_directed h_left_mul h_right_mul h_mul

def nonarchimedean.aux : ring_with_zero_nhd A :=
of_subgroups G h_directed h_left_mul h_right_mul h_mul

lemma nonarchimedean :
  by letI := nonarchimedean.aux G h_directed h_left_mul h_right_mul h_mul;
  exact nonarchimedean A :=
λ U hU,
begin
  rw of_subgroups.nhds_zero at hU,
  rcases hU with ⟨i, hi⟩,
  use G i,
  refine ⟨by apply_instance, _, hi⟩,
  apply of_subgroups.is_open,
end

end of_subgroups

variables {R : Type*} [comm_ring R]

lemma adic_ring.nonarchimedean (I : ideal R) :
  nonarchimedean (I.adic_ring) :=
begin
  intros U hU,
  rw adic_ring.mem_nhds_zero_iff at hU,
  rcases hU with ⟨n, hn⟩,
  exact ⟨_, submodule.submodule_is_add_subgroup _, adic_ring.is_open_pow_ideal _, hn⟩,
end

variables [topological_space R] [topological_ring R]

lemma is_ideal_adic.nonarchimedean {J : ideal R} (h : is-J-adic) :
  nonarchimedean R := by convert adic_ring.nonarchimedean J

lemma is_adic.nonarchimedean (h : is_adic R) :
  nonarchimedean R :=
begin
  rcases h with ⟨J, hJ⟩,
  exact hJ.nonarchimedean
end

lemma nonarchimedean_of_nonarchimedean_embedding
  {R₀ : Type*} [ring R₀] [topological_space R₀] [topological_ring R₀]
  (f : R₀ → R) [is_ring_hom f] (emb : embedding f) (hf : is_open (range f)) (H : nonarchimedean R₀) :
  nonarchimedean R :=
begin
  intros U hU,
  have := H (f ⁻¹' U) _,
  { rcases this with ⟨V, ⟨h₁, h₂, h₃⟩⟩,
    use f '' V,
    resetI,
    split,
    { apply_instance },
    split,
    { exact embedding_open emb hf h₂ },
    { rwa set.image_subset_iff } },
  { apply continuous.tendsto (emb.continuous),
    rwa is_ring_hom.map_zero f }
end
