import topology.algebra.group
import topology.algebra.uniform_ring
import ring_theory.subring

import for_mathlib.topology

universes u v

variables {G : Type u} [add_comm_group G]

open filter set

def prod_map {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}
  (f : α₁ → α₂) (g : β₁ → β₂) : α₁ × β₁ → α₂ × β₂
:= λ p, (f p.1, g p.2)

infix `⨯`:90 := prod_map

def add_group_with_zero_nhd.of_open_add_subgroup
  (H : set G) [is_add_subgroup H] (t : topological_space H) (h : @topological_add_group H t _) :
  add_group_with_zero_nhd G :=
{ Z := (nhds (0 : H)).map $ (subtype.val : H → G),
  zero_Z := calc pure ((0 : H) : G) = map subtype.val (pure 0) : (filter.map_pure _ _).symm
                                ... ≤ _ : map_mono (pure_le_nhds _),
  sub_Z :=
  begin
    let δ_G := λ (p : G × G), p.1 - p.2,
    let δ_H := λ (p : H × H), p.1 - p.2,
    let ι : H → G := subtype.val,
    let N := nhds (0 : H),
    let Z := map subtype.val N,
    change map δ_G (filter.prod Z Z) ≤ Z,
    have key₁: map δ_H (nhds (0, 0)) ≤ N,
    { rw [show N = nhds (δ_H (0, 0)), by simp [*]],
      exact continuous_sub'.tendsto _ },
    have key₂ : δ_G ∘ ι⨯ι = ι ∘ δ_H,
    { ext p,
      change (p.1 : G) - (p.2 : G) = (p.1 - p.2 : G),
      simp [is_add_subgroup.coe_neg, is_add_submonoid.coe_add] },

    calc map δ_G (filter.prod Z Z)
          = map δ_G (map (ι ⨯ ι) $ filter.prod N N) : by rw prod_map_map_eq;refl
      ... = map (δ_G ∘ ι⨯ι) (filter.prod N N)       : map_map
      ... = map (ι ∘ δ_H) (filter.prod N N)         : by rw key₂
      ... = map ι (map δ_H $ filter.prod N N)       : eq.symm map_map
      ... = map ι (map δ_H $ nhds (0, 0))           : by rw ← nhds_prod_eq
      ... ≤ map ι N : map_mono key₁
  end,
  ..‹add_comm_group G› }

def of_open_add_subgroup {G : Type u} [str : add_comm_group G] (H : set G) [is_add_subgroup H]
  (t : topological_space H) (h : @topological_add_group H t _) : topological_space G :=
@add_group_with_zero_nhd.topological_space G
  (add_group_with_zero_nhd.of_open_add_subgroup H t h)

section
variables (G) [topological_space G] [topological_add_group G]

-- This is a hack. That is why it is confined to a section.
-- Making this an attribute on a wider scope is dangerous!
local attribute [instance] topological_add_group.to_uniform_space

-- Wedhorn Definition 5.31 page 38
definition is_complete_hausdorff : Prop := is_complete (univ : set G) ∧ is_hausdorff G

end
