import topology.algebra.ring
import ring_theory.algebra
import ring_theory.ideal_operations

import tactic.abel tactic.chain

import for_mathlib.submodule
import for_mathlib.open_embeddings
import for_mathlib.rings
import topology.algebra.open_subgroup

local attribute [instance] set.pointwise_mul_semiring
local attribute [instance] set.pointwise_mul_action

/--A topological group is non-archimedean if every neighborhood of 1 contains an open subgroup.-/
definition topological_group.nonarchimedean (G : Type*)
  [group G] [topological_space G] [topological_group G] : Prop :=
∀ U ∈ nhds (1 : G), ∃ V : open_subgroup G, (V : set G) ⊆ U

/--A topological additive group is non-archimedean if every neighborhood of 0 contains an
   open subgroup.-/
definition topological_add_group.nonarchimedean (G : Type*)
  [add_group G] [topological_space G] [topological_add_group G] : Prop :=
∀ U ∈ nhds (0 : G), ∃ V : open_add_subgroup G, (V : set G) ⊆ U

attribute [to_additive topological_add_group.nonarchimedean] topological_group.nonarchimedean

namespace topological_group
open function (hiding embedding) set
variables {G₀ : Type*} [group G₀] [topological_space G₀] [topological_group G₀]
variables {G : Type*} [group G] [topological_space G] [topological_group G]
variables (f : G₀ → G) [is_group_hom f]

@[to_additive topological_add_group.nonarchimedean_of_nonarchimedean_open_embedding]
lemma nonarchimedean_of_nonarchimedean_open_embedding
  (emb : topological_space.open_embedding f) (h : nonarchimedean G₀) :
  nonarchimedean G :=
begin
  intros U hU,
  cases h (f ⁻¹' U) _ with V hV,
  { refine ⟨⟨f '' V, _, _⟩, _⟩,
    { exact emb.op _ V.is_open },
    { apply_instance },
    { rwa ← set.image_subset_iff at hV } },
  { apply continuous.tendsto (emb.continuous),
    rwa is_group_hom.map_one f }
end

end topological_group

namespace topological_add_group
namespace nonarchimedean
open topological_ring
variables {R : Type*} [ring R] [topological_space R] [topological_ring R]
variables {S : Type*} [ring S] [topological_space S] [topological_ring S]

lemma left_mul_subset (h : nonarchimedean R) (U : open_add_subgroup R) (r : R) :
  ∃ V : open_add_subgroup R, r • (V : set R) ⊆ U :=
begin
  let V : open_add_subgroup R := ⟨_, _, _⟩,
  { use V,
    intros x hx,
    rw set.mem_smul_set at hx,
    rcases hx with ⟨y, hy, rfl⟩,
    exact hy },
  { apply continuous_mul continuous_const continuous_id,
    exact U.is_open,
    apply_instance },
  { refine {..}; intros,
    { show r * 0 ∈ U, simpa using U.zero_mem },
    { show r * (_ + _) ∈ U, rw left_distrib, apply U.add_mem, assumption' },
    { show r * _ ∈ U, rw mul_neg_eq_neg_mul_symm, apply U.neg_mem, assumption } },
end

lemma prod_subset (hR : nonarchimedean R) (hS : nonarchimedean S) :
  ∀ U ∈ nhds (0 : R × S), ∃ (V : open_add_subgroup R) (W : open_add_subgroup S),
    (V : set R).prod (W : set S) ⊆ U :=
begin
  intros U hU,
  erw [nhds_prod_eq, filter.mem_prod_iff] at hU,
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩,
  cases hR _ hU₁ with V hV,
  cases hS _ hU₂ with W hW,
  use [V, W, set.subset.trans (set.prod_mono hV hW) h]
end

lemma prod_self_subset (hR : nonarchimedean R) :
  ∀ U ∈ nhds (0 : R × R), ∃ (V : open_add_subgroup R), (V : set R).prod (V : set R) ⊆ U :=
begin
  intros U hU,
  rcases prod_subset hR hR U hU with ⟨V, W, h⟩,
  use V ⊓ W,
  refine set.subset.trans (set.prod_mono _ _) ‹_›; simp
end

lemma prod (hR : nonarchimedean R) (hS : nonarchimedean S) :
  nonarchimedean (R × S) :=
begin
  intros U hU,
  rcases prod_subset hR hS U hU with ⟨V, W, h⟩,
  refine ⟨V.sum W, ‹_›⟩
end

lemma mul_subset (h : nonarchimedean R) (U : open_add_subgroup R) :
  ∃ V : open_add_subgroup R, (V : set R) * V ⊆ U :=
begin
  rcases prod_self_subset h _ _ with ⟨V, H⟩,
  use V,
  work_on_goal 0 {
    rwa [set.pointwise_mul_eq_image, set.image_subset_iff] },
  apply mem_nhds_sets (continuous_mul' _ U.is_open),
  simpa only [prod.fst_zero, prod.snd_zero, set.mem_preimage, mul_zero] using U.zero_mem
end

end nonarchimedean
end topological_add_group
