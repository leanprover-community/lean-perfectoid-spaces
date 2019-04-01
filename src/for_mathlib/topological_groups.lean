import topology.algebra.group
import topology.algebra.uniform_ring
import ring_theory.subring

import for_mathlib.topology

universes u v

section
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

end

namespace topological_group
open filter
variables {G : Type*} {H : Type*}
variables [group G] [topological_space G] [topological_group G]
variables [group H] [topological_space H] [topological_group H]
variables (f : G → H) [is_group_hom f]

@[to_additive topological_add_group.continuous_of_continuous_at_zero]
lemma continuous_of_continuous_at_one (h : continuous_at f 1) :
  continuous f :=
begin
  rw continuous_iff_continuous_at,
  intro g,
  have hg : continuous (λ x, g⁻¹ * x) :=
    continuous_mul continuous_const continuous_id,
  have hfg : continuous (λ x, f g  * x) :=
    continuous_mul continuous_const continuous_id,
  convert tendsto.comp _ (tendsto.comp h _),
  swap 4,
  { simpa only [mul_left_inv] using hg.tendsto g },
  swap 3,
  { dsimp [function.comp],
    simpa only [mul_left_inv] using hfg.tendsto (f 1) },
  { funext x,
    delta function.comp,
    rw [is_group_hom.mul f, is_group_hom.inv f, ← mul_assoc, mul_right_inv, one_mul] },
end

end topological_group


section
open set
variables (G : Type u) [add_comm_group G] [topological_space G] [topological_add_group G]

-- This is a hack. That is why it is confined to a section.
-- Making this an attribute on a wider scope is dangerous!
local attribute [instance] topological_add_group.to_uniform_space

-- Wedhorn Definition 5.31 page 38
definition is_complete_hausdorff : Prop := is_complete (univ : set G) ∧ is_hausdorff G

end
