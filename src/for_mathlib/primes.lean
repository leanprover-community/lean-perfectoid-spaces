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
lemma not_dvd_one : ¬ (p : ℕ) ∣ 1 := p.2.not_dvd_one

end primes
end nat

instance monoid.prime_pow {α : Type*} [monoid α]: has_pow α nat.primes := ⟨λ x p, x^p.val⟩
