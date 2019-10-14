import for_mathlib.nnreal

import valuation.topology
import Huber_pair
import Frobenius

set_option old_structure_cmd true -- do we do this or not?

namespace valuation
variables {R : Type*} [comm_ring R]
variables {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]

local attribute [instance] classical.decidable_linear_order

def le_one_subring (v : valuation R Γ₀) := {r : R | v r ≤ 1}

instance le_one_subring.is_subring (v : valuation R Γ₀) : is_subring v.le_one_subring :=
-- @subtype.comm_ring R _ {r : R | v r ≤ 1}
{ zero_mem := show v 0 ≤ 1, by simp,
  one_mem := show v 1 ≤ 1, by simp,
  add_mem := λ r s (hr : v r ≤ 1) (hs : v s ≤ 1), show v (r+s) ≤ 1,
  by calc v (r + s) ≤ max (v r) (v s) : v.map_add r s
                ... ≤ 1 : max_le hr hs,
  neg_mem := λ r (hr : v r ≤ 1), show v (-r) ≤ 1, by rwa [v.map_neg],
  mul_mem := λ r s (hr : v r ≤ 1) (hs : v s ≤ 1), show v (r*s) ≤ 1,
  begin
    rw v.map_mul,
    refine le_trans (actual_ordered_comm_monoid.mul_le_mul_right' hr) _,
    rwa one_mul
  end }

instance coe_nat_le_one_subring (v : valuation R Γ₀) :
  has_coe ℕ v.le_one_subring := by apply_instance

end valuation

class nondiscrete_valued_field (K : Type*) extends discrete_field K :=
(v : valuation K nnreal)
(non_discrete : ∀ ε : nnreal, 0 < ε → ∃ x : K, 1 < v x ∧ v x < 1 + ε)

noncomputable instance foo {K : Type}
  [nondiscrete_valued_field K] : valued K :=
{ Γ₀ := nnreal,
  v := nondiscrete_valued_field.v K}

-- Currently we know that clsp is a complete uniform topological field.
-- And this all comes from the completion machine

open function nat

local attribute [instance] valued.uniform_space valued.uniform_add_group
local notation `v` := valued.value

noncomputable example (K : Type) [nondiscrete_valued_field K] : uniform_space K
:= by apply_instance

-- separated should follow from the fact that the kernel of v is 0
-- but I don't know how to steer it and I don't know if we need it.

instance nondiscrete_valued_field.separated (K : Type) [nondiscrete_valued_field K] :
  separated K := sorry

local attribute [instance, priority 1000] comm_ring.to_ring

class is_perfectoid_field (K : Type) [nondiscrete_valued_field K] (p : primes) : Prop :=
[complete : complete_space K]
(Frobenius : surjective (Frob (valued.v K).le_one_subring ∕p))

-- Let K be the completion of the perfection of (Z/pZ)((t)). [done]
-- Show that K is a perfectoid field
-- show a perfectoid field is a perfectoid ring
-- Show that Spa(K) is a perfectoid space.

-- is a valued R a Huber ring?

theorem perfectoid_field.huber_ring (K : Type) (p : primes)
  [nondiscrete_valued_field K] [is_perfectoid_field K p] : Huber_ring K := sorry
