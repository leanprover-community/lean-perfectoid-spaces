import valuations 
import analysis.topology.topological_space

universes u v

open is_valuation 

definition Spv (R : Type u) [comm_ring R] := 
{ineq : R → R → Prop // ∃ (Γ : Type u) [linear_ordered_comm_group Γ],
  by exactI ∃ (v : valuation R Γ), ∀ r s : R, ineq r s ↔ v r ≤ v s}

-- TODO (if I understood Mario correctly):
-- definition Spv.mk (A : Type u) [comm_ring A] (Γ : Type v) -- note : not type u 
-- [linear_ordered_comm_group Γ] : Spv A := 
-- this is a set-theoretic issue: I need to find Gamma' of type u to push this through 

namespace Spv 

variables {A : Type*} [comm_ring A]

definition basic_open (r s : A) : set (Spv A) := 
{v | v.val r s ∧ ¬ v.val s 0}

instance (A : Type*) [comm_ring A] : topological_space (Spv A) :=
topological_space.generate_from {U : set (Spv A) | ∃ r s : A, U = basic_open r s}

end Spv 
