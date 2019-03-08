import data.list.basic
import topology.algebra.topological_structures
import ring_theory.subring
import group_theory.subgroup
import tactic.tfae

import for_mathlib.topological_rings
import power_bounded

-- f-adic rings are called Huber rings by Scholze.
-- Topological ring A contains on open subring A0 such that the subspace topology on A0 is
-- I-adic, where I is a finitely generated ideal of A0 .

universe u

section
variables (A : Type u) [comm_ring A] [topological_space A] [topological_ring A]

structure Huber_ring.pair_of_definition :=
(A₀   : set A)
[Hr   : is_subring A₀]
(Ho   : is_open A₀)
(J    : ideal A₀)
(gen  : set A₀)
(fin  : fintype gen)
(span : ideal.span gen = J)
(top  : @is_ideal_adic _ (subset.comm_ring) _ (topological_subring A₀) J)

class Huber_ring (A : Type u) extends comm_ring A, topological_space A, topological_ring A :=
(pod : nonempty $ Huber_ring.pair_of_definition A)

end

namespace Huber_ring

variables (A : Type u) [Huber_ring A]

/-- An alternative definition. This deduces the property. The constructor is given below.
(Wedhorn, prop+def 6.1.) -/
lemma alt_def :
  ∃ U T : set A, T ⊆ U ∧ set.finite T ∧
  (filter.generate {U' : set A | ∃ n : pnat, U' = {x | ∃ y ∈ U, y^(n:ℕ) = x}} = (nhds 0)) ∧
  add_group.closure {y : A | ∃ (t ∈ T) (u ∈ U), y = t * u} =
  add_group.closure {y : A | ∃ (u₁ ∈ U) (u₂ ∈ U), y = u₁ * u₂} ∧
  add_group.closure {y : A | ∃ (t ∈ U) (u ∈ U), y = t * u} ⊆ U :=
begin
  rcases Huber_ring.pod A with ⟨⟨A₀, Hr, Ho, J, gen, fin, span, top⟩⟩,
  resetI,
  use [subtype.val '' J.carrier, subtype.val '' gen],
  have gensubJ : subtype.val '' gen ⊆ subtype.val '' J.carrier,
  { apply set.image_subset,
    rw ← span,
    convert ideal.subset_span, },
  refine ⟨gensubJ, set.finite_image _ ⟨fin⟩, _, _, _⟩,
  { apply le_antisymm,
    { sorry },
    { sorry } },
  { sorry },
  { --have := is_add_group_hom.image_add_subgroup subtype.val J.carrier,
    apply add_group.closure_subset, }
end

def is_ring_of_definition (A₀ : set A) : Prop :=
∃ pod : pair_of_definition A, A₀ = pod.A₀

namespace is_ring_of_definition
open list

-- Wedhorn, lemma 6.2.
lemma tfae (A₀ : set A) [is_subring A₀] :
tfae [is_ring_of_definition A₀, (is_open A₀ ∧ is_adic A₀), (is_open A₀ ∧ is_bounded A₀)] :=
begin
  tfae_have : 1 → 2,
  { rintro ⟨pod, h⟩,
    tactic.unfreeze_local_instances,
    subst h,
    exact ⟨pod.Ho, ⟨pod.J, pod.top⟩⟩ },
  tfae_have : 2 → 3,
  { rintros ⟨hl, hr⟩,
    refine ⟨hl, _⟩,
    intros U hU,
    rw nhds_sets at hU,
    rcases hU with ⟨U', U'_sub, ⟨U'_open, U'_0⟩⟩,
    rcases hr with ⟨J, h1, h2⟩,
    have H : (∃ (n : ℕ), (J^n).carrier ⊆ {a : A₀ | a.val ∈ U'}) :=
      h2 {a | a.val ∈ U'} U'_0 (continuous_subtype_val _ U'_open),
    rcases H with ⟨n, hn⟩,
    use coe '' (J^n).carrier, -- the key step
    split,
    { apply mem_nhds_sets,
      { refine embedding_open embedding_subtype_val _ (h1 n),
        rw set.range_coe_subtype,
        exact hl },
      { exact ⟨0, (J^n).zero_mem, rfl⟩ } },
    { rintros a ⟨a₀, ha₀⟩ b hb,
      apply U'_sub,
      rw ← ha₀.right,
      exact hn ((J^n).mul_mem_right ha₀.left : (a₀ * ⟨b,hb⟩) ∈ J^n) } },
  tfae_have : 3 → 1,
  { rintro ⟨hl, hr⟩,
    refine ⟨⟨A₀, hl, _, _, _, _, _⟩, rfl⟩,
    sorry },
  tfae_finish
end

end is_ring_of_definition


namespace Huber_ring

-- Wedhorn, lemma 6.1.
lemma tfae : (∃ U T : set A, T ⊆ U ∧ set.finite T ∧
(filter.generate {U' : set A | ∃ n : pnat, U' = {x | ∃ y ∈ U, y^(n:ℕ) = x}} = (nhds 0)) ∧
{y : A | ∃ (t ∈ T) (u ∈ U), y = t * u} = {y : A | ∃ (u₁ ∈ U) (u₂ ∈ U), y = u₁ * u₂} ∧
{y : A | ∃ (t ∈ U) (u ∈ U), y = t * u} ⊆ U) ↔
(∃ (A₀ : set A) [h : is_subring A₀], by haveI := h; exact is_ring_of_definition A₀) :=
begin
  split,
  { rintro ⟨U, T, Tsub, Tfin, hnhds, hTU, hU2⟩,
    let W := add_group.closure U,
    have hU : is_open U,
    { -- is this provable, or should it have been an assumption?
      sorry },
    have hW : is_open W,
    { sorry },
    existsi (add_group.closure (W ∪ {1})),
    split,
    { split,
      sorry,
      sorry },
    { sorry } },
  { rintro ⟨A₀, hA₀, A₀_open, J, gen, ⟨hgen₁, hgen₂⟩, h1, h2⟩,
    haveI := hA₀,
    use [subtype.val '' J.carrier, subtype.val '' gen],
    have gensubJ : subtype.val '' gen ⊆ subtype.val '' J.carrier,
    { apply set.image_subset,
      rw ← hgen₂,
      convert ideal.subset_span, },
    refine ⟨gensubJ, set.finite_image _ hgen₁, _, _, _⟩,
    { apply le_antisymm,
      { sorry },
      { sorry } },
    { ext x, split;
      rintros ⟨t, ht, u, hu, H⟩,
      { exact ⟨t, (gensubJ ht), u, hu, H⟩ },
      sorry },
    { rintros x ⟨x₀val, ⟨x₀, hx₀⟩, ⟨uval, ⟨u, hu⟩, hx⟩⟩,
      refine ⟨x₀ * u, _, _⟩,
      { apply J.mul_mem_right, exact hx₀.left },
      { rw [hx, ← hx₀.right, ← hu.right], refl } } }
end

variables [Huber_ring A]

instance power_bounded_add_subgroup : is_add_subgroup (power_bounded_subring A) :=
{ zero_mem := power_bounded.zero_mem A,
  add_mem := assume a b a_in b_in U U_nhds,begin
    sorry
  end,
  neg_mem := λ a, power_bounded.neg_mem A }

instance : is_subring (power_bounded_subring A) :=
{..power_bounded.submonoid A, ..Huber_ring.power_bounded_add_subgroup}

instance nat.power_bounded: has_coe ℕ (power_bounded_subring A) := ⟨nat.cast⟩

instance int.power_bounded: has_coe ℤ (power_bounded_subring A) := ⟨int.cast⟩
end Huber_ring
