import valuation.field
import valuation.canonical

/-!
# The valuation on the completion of the valuation field

In this file we extend the canonical valuation on the the valuation field of (R, v) to its
completion (for the topological field structure coming from the valuation).
-/

noncomputable theory

open valuation uniform_space
local attribute [instance] valued.subgroups_basis valued.uniform_space

variables {Γ : Type*} [linear_ordered_comm_group Γ] {R : Type*} [comm_ring R] (v : valuation R Γ)

instance valuation_field.valued : valued (valuation_field v) :=
⟨value_group v, valuation_field.canonical_valuation v⟩

instance valuation_field.topology : topological_space (valuation_field v) :=
subgroups_basis.topology _

instance valuation_field.top_ring : topological_ring (valuation_field v) :=
ring_filter_basis.is_topological_ring _ rfl

instance valuation_field.uniform_add_group : uniform_add_group (valuation_field v) :=
topological_add_group_is_uniform

instance valuation_field.comm_ring_completion : comm_ring (completion $ valuation.valuation_field v) :=
completion.comm_ring _

instance valuation_field.ring_completion : ring (completion $ valuation.valuation_field v) :=
comm_ring.to_ring _

/--The valuation on the completion of the valuation field of a valued ring.-/
def valuation_on_completion (v : valuation R Γ) :
  valuation (completion $ valuation.valuation_field v) (value_group v) :=
⟨valued.extension, valued.extension_is_valuation⟩

instance valuation_field.completion_valued : valued (completion $ valuation_field v) :=
⟨value_group v, valuation_on_completion v⟩
