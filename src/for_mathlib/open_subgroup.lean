import topology.algebra.open_subgroup

open topological_space
variables (G : Type*) [group G] [topological_space G] [topological_group G]

namespace open_subgroup

def of_mem_nhds {s : set G} [is_subgroup s] (h : s ∈ nhds (1 : G)) : open_subgroup G :=
⟨s,
 is_open_of_nonempty_open_subset (by { rcases mem_nhds_sets_iff.mp h with ⟨U, UG, U_op, one_U⟩,
   exact ⟨⟨U, U_op⟩, ⟨⟨(1 : G), one_U⟩⟩, UG⟩ }),
 by apply_instance⟩

attribute [to_additive open_add_subgroup.of_mem_nhds._proof_1] of_mem_nhds._proof_1
attribute [to_additive open_add_subgroup.of_mem_nhds] of_mem_nhds

end open_subgroup

attribute [to_additive open_add_subgroup.mem_nhds_zero] open_subgroup.mem_nhds_one
