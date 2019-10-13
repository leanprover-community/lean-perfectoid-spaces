import valuation.topology
import examples.char_p
import Frobenius

set_option old_structure_cmd true -- do we do this or not?

class nondiscrete_valued_field (K : Type*) extends discrete_field K :=
(v : valuation K nnreal)
(non_discrete : ∀ ε : nnreal, 0 < ε → ∃ x : K, 1 < v x ∧ v x < 1 + ε)

noncomputable instance foo {K : Type}
  [nondiscrete_valued_field K] : valued K :=
{ Γ₀ := nnreal,
  v := nondiscrete_valued_field.v K}

--  Currently we know that clsp is a complete uniform topological field.
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
  [nondiscrete_valued_field K] [is_perfectoid_field K p] : Huber_ring K :=
