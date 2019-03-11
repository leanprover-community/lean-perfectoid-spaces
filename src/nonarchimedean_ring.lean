import topology.algebra.ring
import ring_theory.subring

import for_mathlib.adic_topology
import for_mathlib.topological_rings

/- A commutative topological ring is _non-archimedean_ if every open subset
   containing 0 also contains an open additive subgroup.
-/

definition nonarchimedean (G : Type*)
  [add_group G] [topological_space G] [topological_add_group G] : Prop :=
∀ U ∈ nhds (0 : G), ∃ V : set G, is_add_subgroup V ∧ is_open V ∧ V ⊆ U

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

lemma nonarchimedean_of_nonarchimedean_subring (R₀ : set R) [is_subring R₀]
  (h : is_open R₀) (H : nonarchimedean R₀) : nonarchimedean R :=
begin
  intros U hU,
  have := H (subtype.val ⁻¹' U) _,
  { rcases this with ⟨V, hV⟩,
    use subtype.val '' V,
    split,
    { refine @is_add_group_hom.image_add_subgroup _ _ _ _ subtype.val
        ⟨λ x y, show (x + y).val = x.val + y.val, from _⟩ V hV.1,
      refl, },
    { split,
      { apply embedding_open embedding_subtype_val,
        { rw subtype.val_range,
          exact h, },
        { exact hV.2.1 } },
      { rw set.image_subset_iff,
        exact hV.2.2 } } },
  { apply continuous.tendsto (continuous_subtype_val),
    exact hU }
end
