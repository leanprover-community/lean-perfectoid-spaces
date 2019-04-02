import topology.algebra.ring
import ring_theory.subring

import tactic.tidy

import for_mathlib.subgroup
import for_mathlib.adic_topology
import for_mathlib.top_ring
import for_mathlib.topological_rings

open set
/-
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

namespace nonarchimedean
open topological_ring
variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]
variables {S : Type*} [comm_ring S] [topological_space S] [topological_ring S]

lemma open_add_subgroups_directed (h : nonarchimedean R) (U₁ U₂ : open_add_subgroups R) :
  ∃ U : open_add_subgroups R, U.1 ⊆ U₁.1 ∩ U₂.1 :=
begin
  let U : open_add_subgroups R := ⟨_, _, _⟩,
  { use U },
  { apply is_add_subgroup.inter },
  { exact is_open_inter U₁.2.2 U₂.2.2 }
end

lemma left_mul_subset (h : nonarchimedean R) (U : open_add_subgroups R) (r : R) :
  ∃ V : open_add_subgroups R, (λ x : R, r * x) '' V.1 ⊆ U.1 :=
begin
  let V : open_add_subgroups R := ⟨_, _, _⟩,
  { use V,
    rw set.image_subset_iff },
  { letI : is_add_group_hom (λ (x : R), r * x) :=
      ⟨λ _ _, left_distrib _ _ _⟩,
    apply_instance },
  { apply continuous_mul_left,
    exact U.2.2 }
end

lemma prod.aux (hR : nonarchimedean R) (hS : nonarchimedean S) :
  ∀ U ∈ nhds (0 : R × S), ∃ (V : set R) (W : set S),
    is_add_subgroup V ∧ is_open V ∧ is_add_subgroup W ∧ is_open W ∧ V.prod W ⊆ U :=
begin
  intros U hU,
  rw [show (0 : R × S) = (0,0), from rfl] at hU,
  rw nhds_prod_eq at hU,
  rw filter.mem_prod_iff at hU,
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩,
  rcases hR _ hU₁ with ⟨V, _, _, _⟩,
  rcases hS _ hU₂ with ⟨W, _, _, _⟩,
  refine ⟨V, W, ‹_›, ‹_›, ‹_›, ‹_›, _⟩,
  { refine set.subset.trans (set.prod_mono _ _) h; assumption }
end

lemma prod.aux' (hR : nonarchimedean R) :
  ∀ U ∈ nhds (0 : R × R), ∃ (V : set R), is_add_subgroup V ∧ is_open V ∧ V.prod V ⊆ U :=
begin
  intros U hU,
  rcases prod.aux hR hR U hU with ⟨V, W, _, _, _, _, _⟩,
  refine ⟨V ∩ W, _, _, _⟩,
  { resetI, apply_instance },
  { apply is_open_inter; assumption },
  { refine set.subset.trans (set.prod_mono _ _) ‹_›; simp },
end

lemma prod (hR : nonarchimedean R) (hS : nonarchimedean S) :
  nonarchimedean (R × S) :=
begin
  intros U hU,
  rcases prod.aux hR hS U hU with ⟨V, W, _, _, _, _, _⟩,
  refine ⟨V.prod W, _, _, ‹_›⟩,
  { resetI, apply_instance },
  { apply is_open_prod; assumption }
end

lemma mul_subset (h : nonarchimedean R) (U : open_add_subgroups R) :
  ∃ V : open_add_subgroups R, (λ x : R × R, x.1*x.2) '' (set.prod V.1 V.1) ⊆ U.1 :=
begin
  rcases prod.aux' h _ _ with ⟨V, _, _, H⟩,
  refine ⟨⟨V, ‹_›, ‹_›⟩, _⟩,
  work_on_goal 0 {
    rw set.image_subset_iff,
    refine set.subset.trans (set.prod_mono _ _) H; simp [le_refl] },
  { apply mem_nhds_sets,
    { apply continuous_mul',
      cases U,
      tauto },
    { rw mem_preimage_eq,
      convert is_add_submonoid.zero_mem _,
      { simp },
      { apply_instance } } }
end

end nonarchimedean

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
-/
