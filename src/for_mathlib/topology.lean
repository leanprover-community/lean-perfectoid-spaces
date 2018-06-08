import analysis.topology.topological_space

@[class] def opens (X : Type*) [topological_space X] := {U : set X // is_open U}

namespace opens

variables (X : Type*) [topological_space X]

instance : has_coe (opens X) (set X) := ⟨λU, U.1⟩

instance : has_mem X (opens X) := ⟨λx U, x ∈ U.1⟩

end opens