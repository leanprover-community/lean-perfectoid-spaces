import data.nat.prime
import ring_theory.ideals

open nat

instance : has_coe primes ℕ := ⟨subtype.val⟩
instance monoid.prime_pow {α : Type*} [monoid α]: has_pow α primes := ⟨λ x p, x^p.val⟩
