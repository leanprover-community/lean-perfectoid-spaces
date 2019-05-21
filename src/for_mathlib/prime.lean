-- The important contents of this file have been PR'd to mathlib in #1071
-- Instead of a class, in the PR `Prime` is a subtype.
-- This should not cause any problems.

import data.nat.prime 

namespace nat

class Prime :=
(p : ℕ) (pp : nat.prime p)

-- unit test

definition two' : Prime := ⟨2,prime_two⟩

instance Prime_is_nat : has_coe Prime ℕ := ⟨λ P, P.p⟩

-- unit test

example : (two' : ℕ) = 2 := rfl

end nat 

class is_prime (p : ℕ) : Prop := 
(Hp : nat.prime p)


