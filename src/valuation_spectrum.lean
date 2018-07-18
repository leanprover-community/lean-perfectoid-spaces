--import data.equiv.basic
import valuations 
import analysis.topology.topological_space

open is_valuation 

definition Spv (A : Type*) [comm_ring A] := 
{ineq : A → A → Prop // ∃ (Γ : Type*) [linear_ordered_comm_group Γ],
  by exactI ∃ (v : valuation A Γ), ∀ r s : A, ineq r s ↔ v r ≤ v s}

namespace Spv 

variables {A : Type*} [comm_ring A]

definition basic_open (r s : A) : set (Spv A) := 
  {v | v.val r s ∧ ¬ v.val s 0}

--  quotient.lift (λ v, valuations.f v r ≤ v.f s ∧ v.f s > 0) (λ v w H,propext begin 
--  dsimp,
--  rw basic_open.aux1 r s v w H,
--  rw basic_open.aux2 s v w H,
--  end)
--  (λ v w H, show (v(r) ≤ v(s) ∧ v(s) > 0) ↔ (w(r) ≤ w(s) ∧ w(s) > 0) _

instance (A : Type*) [comm_ring A] : topological_space (Spv A) :=
  topological_space.generate_from {U : set (Spv A) | ∃ r s : A, U = basic_open r s}

end Spv 

