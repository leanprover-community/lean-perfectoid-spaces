/-
 Lemmas in this file are currently not used in the perfectoid spaces project, but they
 were once thought to be useful, and could be PR'ed into mathlib anyway.
-/

import analysis.topology.topological_space
import for_mathlib.completion


section uniform_space
open uniform_space
variables {α : Type*} [uniform_space α]
local attribute [instance] separation_setoid

instance inhabited_separation_space [h : inhabited α] : 
  inhabited (quotient (separation_setoid α)) := ⟨⟦h.default⟧⟩

instance inhabited_completion [inhabited α] : inhabited (completion α) := 
by unfold completion; apply_instance
end uniform_space