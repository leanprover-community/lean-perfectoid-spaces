import analysis.topology.topological_structures
import ring_theory.subring
import for_mathlib.ideals
import for_mathlib.bounded
import for_mathlib.topological_rings

-- f-adic rings are called Huber rings by Scholze.
-- Topological ring A contains on open subring A0 such that the subspace topology on A0 is
-- I-adic, where I is a finitely generated ideal of A0 .

universe u

variables {A : Type u} [comm_ring A] [topological_space A] [topological_ring A]

def is_ring_of_definition (A₀ : set A) [is_subring A₀] : Prop :=
is_open A₀ ∧ (∃ (J : set A₀) [hJ : is_ideal J] (gen : set A₀), (set.finite gen ∧ span gen = J) ∧
(by haveI := topological_subring A₀; haveI := hJ; exact is_ideal_adic J))

namespace is_ring_of_definition

-- Wedhorn, lemma 6.1. (i) → (ii)
lemma tfae_i_to_ii : (∃ U T : set A, T ⊆ U ∧ set.finite T ∧
(filter.generate {U' : set A | ∃ n : pnat, U' = {x | ∃ y : A, y^(n:ℕ) = x}} = (nhds 0)) ∧
{y : A | ∃ (t ∈ T) (u ∈ U), y = t * u} = {y : A | ∃ (t ∈ U) (u ∈ U), y = t * u} ∧ 
{y : A | ∃ (t ∈ U) (u ∈ U), y = t * u} ⊆ U) →
(∃ (A₀ : set A) [h : is_subring A₀], by haveI := h; exact is_ring_of_definition A₀) :=
begin
 rintro ⟨U, T, Tsub, Tfin, hnhds, hTU, hU2⟩,
 sorry
end

-- Wedhorn, lemma 6.1. (1) → (3)
lemma tfae_1_to_3 (A₀ : set A) [is_subring A₀] : is_ring_of_definition A₀ → (is_open A₀ ∧ is_bounded A₀) :=
begin
  rintro ⟨hl, J, hJ, gen, hgen, h1, h2⟩,
  split, exact hl,
  intros U hU,
  rw nhds_sets at hU,
  rcases hU with ⟨U', U'_sub, ⟨U'_open, U'_0⟩⟩,
  have H : (∃ (n : ℕ), pow_ideal J n ⊆ {a : ↥A₀ | a.val ∈ U'}) :=
    h2 {a | a.val ∈ U'} U'_0 (continuous_subtype_val _ U'_open),
  rcases H with ⟨n, hn⟩,
  haveI := @pow_ideal.is_ideal _ _ J hJ n, -- so annoying
  existsi subtype.val '' (pow_ideal J n),  -- the key step
  split,
  { apply mem_nhds_sets,
    { refine embedding_open embedding_subtype_val _ (h1 n),
      rw set.subtype_val_range,
      exact hl },
    have H := @is_submodule.zero _ _ _ _ (pow_ideal J n) _,
    split, split, exact H, refl },
  rintros a ⟨a₀, ha₀⟩ b hb,
  apply U'_sub,
  have : a₀.val * b ∈ U':= hn (is_ideal.mul_right ha₀.left : (a₀ * ⟨b,hb⟩) ∈ pow_ideal J n),
  rwa ha₀.right at this
end

lemma tfae_3_to_1 (A₀ : set A) [is_subring A₀] : is_ring_of_definition A₀ → (is_open A₀ ∧ is_bounded A₀) :=
begin
  rintro ⟨hl, J, hJ, gen, hgen, h1, h2⟩,
  split, exact hl,
  intros U hU,
  rw nhds_sets at hU,
  rcases hU with ⟨U', U'_sub, ⟨U'_open, U'_0⟩⟩,
  have H : (∃ (n : ℕ), pow_ideal J n ⊆ {a : ↥A₀ | a.val ∈ U'}) :=
    h2 {a | a.val ∈ U'} U'_0 (continuous_subtype_val _ U'_open),
  rcases H with ⟨n, hn⟩,
  haveI := @pow_ideal.is_ideal _ _ J hJ n, -- so annoying
  existsi subtype.val '' (pow_ideal J n),  -- the key step
  split,
  { apply mem_nhds_sets,
    { refine embedding_open embedding_subtype_val _ (h1 n),
      rw set.subtype_val_range,
      exact hl },
    have H := @is_submodule.zero _ _ _ _ (pow_ideal J n) _,
    split, split, exact H, refl },
  rintros a ⟨a₀, ha₀⟩ b hb,
  apply U'_sub,
  have : a₀.val * b ∈ U':= hn (is_ideal.mul_right ha₀.left : (a₀ * ⟨b,hb⟩) ∈ pow_ideal J n),
  rwa ha₀.right at this
end

end is_ring_of_definition

class Huber_ring (A : Type u) extends comm_ring A, topological_space A, topological_ring A :=
(A₀ : set A)
[HA₀ : is_subring A₀]
(A₀_is_ring_of_definition : is_ring_of_definition A₀)
