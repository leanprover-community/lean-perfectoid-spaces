import topology.algebra.group
import topology.algebra.uniform_group

universes u v

variables {G : Type u} [add_comm_group G]

open filter set

def add_group_with_zero_nhd.of_open_add_subgroup
  (H : set G) [is_add_subgroup H] (t : topological_space H) (h : @topological_add_group H t _) :
  add_group_with_zero_nhd G :=
{ Z := (nhds (0 : H)).map $ (subtype.val : H → G),
  zero_Z := λ U hU, mem_pure $ by {rw mem_map at hU, have := mem_of_nhds hU, exact this },
  sub_Z :=
  begin
    rw tendsto_prod_self_iff,
    rintros U hU,
    rw mem_map at hU,
    rcases exists_nhds_half_neg hU with ⟨V, h₁, h₂⟩,
    use [subtype.val '' V, image_mem_map h₁],
    rintros x y ⟨x₀, hx₁, hx₂⟩ ⟨y₀, hy₁, hy₂⟩,
    erw [← hx₂, ← hy₂],
    simpa using h₂ _ _ hx₁ hy₁,
  end,
  ..‹add_comm_group G› }

def of_open_add_subgroup {G : Type u} [str : add_comm_group G] (H : set G) [is_add_subgroup H]
  (t : topological_space H) (h : @topological_add_group H t _) : topological_space G :=
@add_group_with_zero_nhd.topological_space G
  (add_group_with_zero_nhd.of_open_add_subgroup H t h)
