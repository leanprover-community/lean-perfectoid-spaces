import analysis.topology.topological_space

section opens

variables (X : Type*) [topological_space X]
include X

@[class] def opens := {U : set X // is_open U}

instance : has_coe (opens X) (set X) := ⟨λU, U.1⟩

instance : has_mem X (opens X) := ⟨λx U, x ∈ U.1⟩

end opens