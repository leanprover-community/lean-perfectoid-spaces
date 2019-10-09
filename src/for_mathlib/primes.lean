import data.nat.prime
import ring_theory.ideals

import for_mathlib.char_p

namespace nat
namespace primes
variable (p : primes)

instance : has_coe primes ℕ := ⟨subtype.val⟩

lemma ne_zero : (p : ℕ) ≠ 0 := p.2.ne_zero
lemma ne_one : (p : ℕ) ≠ 1 := p.2.ne_one
lemma one_lt : 1 < (p : ℕ) := p.2.one_lt

end primes
end nat

instance monoid.prime_pow {α : Type*} [monoid α]: has_pow α nat.primes := ⟨λ x p, x^p.val⟩

section
variables (p : nat.primes) (R : Type*) [semiring R] [char_p R p]
include p

lemma ring_char.prime : nat.prime (ring_char R) :=
by { rw ← ring_char.eq R ‹_›, exact p.2 }

end

instance ring_char.char (R : Type*) [semiring R] : char_p R (ring_char R) :=
{ cast_eq_zero_iff := ring_char.spec R }
