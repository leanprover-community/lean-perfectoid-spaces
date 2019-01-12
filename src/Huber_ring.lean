import analysis.topology.topological_structures
import ring_theory.subring
import tactic.tfae
import data.list.basic
import for_mathlib.topological_rings
import power_bounded

-- f-adic rings are called Huber rings by Scholze.
-- Topological ring A contains on open subring A0 such that the subspace topology on A0 is
-- I-adic, where I is a finitely generated ideal of A0 .

universe u

variables {A : Type u} [comm_ring A] [topological_space A] [topological_ring A]

def is_ring_of_definition (A₀ : set A) [is_subring A₀] : Prop :=
is_open A₀ ∧ (∃ (J : ideal A₀) (gen : set A₀), (set.finite gen ∧ ideal.span gen = J) ∧
(by haveI := topological_subring A₀; exact is-J-adic))

namespace is_ring_of_definition
open list

-- Wedhorn, lemma 6.2.
lemma tfae (A₀ : set A) [is_subring A₀] :
tfae [is_ring_of_definition A₀, (is_open A₀ ∧ is_adic A₀), (is_open A₀ ∧ is_bounded A₀)] :=
begin
  tfae_have : 1 → 2,
  { rintro ⟨hl, J, gen, hgen, h⟩,
    exact ⟨hl, ⟨J, h⟩⟩ },
  tfae_have : 2 → 3,
  { rintros ⟨hl, hr⟩,
    split, exact hl,
    intros U hU,
    rw nhds_sets at hU,
    rcases hU with ⟨U', U'_sub, ⟨U'_open, U'_0⟩⟩,
    rcases hr with ⟨J, h1, h2⟩,
    have H : (∃ (n : ℕ), (J^n).carrier ⊆ {a : A₀ | a.val ∈ U'}) :=
      h2 {a | a.val ∈ U'} U'_0 (continuous_subtype_val _ U'_open),
    rcases H with ⟨n, hn⟩,
    existsi subtype.val '' (J^n).carrier,  -- the key step
    split,
    { apply mem_nhds_sets,
      { refine embedding_open embedding_subtype_val _ (h1 n),
        rw set.subtype_val_range,
        exact hl },
      simp [(is_subring.to_is_add_subgroup A₀).zero_mem], 
      exact (J^n).zero_mem },
    rintros a ⟨a₀, ha₀⟩ b hb,
    apply U'_sub,
    have : a₀.val * b ∈ U':= hn ((J^n).mul_mem_right ha₀.left : (a₀ * ⟨b,hb⟩) ∈ J^n),
    rwa ha₀.right at this },
  tfae_have : 3 → 1,
  { rintro ⟨hl, hr⟩,
    split, exact hl,
    sorry },
  tfae_finish
end

end is_ring_of_definition

class Huber_ring (A : Type u) extends comm_ring A, topological_space A, topological_ring A :=
(A₀ : set A)
[HA₀ : is_subring A₀]
(A₀_is_ring_of_definition : is_ring_of_definition A₀)

namespace Huber_ring

-- Wedhorn, lemma 6.1.
lemma tfae : (∃ U T : set A, T ⊆ U ∧ set.finite T ∧
(filter.generate {U' : set A | ∃ n : pnat, U' = {x | ∃ y ∈ U, y^(n:ℕ) = x}} = (nhds 0)) ∧
{y : A | ∃ (t ∈ T) (u ∈ U), y = t * u} = {y : A | ∃ (t ∈ U) (u ∈ U), y = t * u} ∧ 
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
  { rintro ⟨A₀, hA₀, A₀_open, J, gen, hgen, h1, h2⟩,
    haveI := hA₀,
    use subtype.val '' J.carrier,
    existsi subtype.val '' gen,
    have gensubJ : subtype.val '' gen ⊆ subtype.val '' J.carrier,
    { have : gen ⊆ J,
      rw ← hgen.right,
      exact ideal.subset_span,
      rintros x ⟨x₀, hx1, hx2⟩,
      exact ⟨x₀, this hx1,hx2⟩ },
    refine ⟨gensubJ, set.finite_image _ hgen.left, _⟩,
    split,
    { apply le_antisymm,
      { sorry },
      { sorry } },
    split,
    { ext x, split;
      rintros ⟨t, ht, u, hu, H⟩,
      { exact ⟨t, (gensubJ ht), u, hu, H⟩ },
      sorry },
    { rintros x ⟨x₀, hx1, hx2⟩,
      sorry } }
end

end Huber_ring
