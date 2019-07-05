import algebra.char_p
import ring_theory.ideals

-- I think this paragraph should be removable. BUt Lean doesn't agree.
-- The next two lines have been PR'd to mathlib in #1073
def Prime := { p : ℕ // p.prime }
instance : has_coe Prime ℕ := ⟨subtype.val⟩
instance monoid.Prime_pow {α : Type*} [monoid α]: has_pow α Prime := ⟨λ x p, x^p.val⟩

instance monoid.prime_pow {α : Type*} [monoid α]: has_pow α nat.primes := ⟨λ x p, x^p.val⟩

noncomputable def Frobenius (α : Type*) [semiring α] : α → α := λ x, x^(ring_char α)
notation `Frob` R `∕` x := Frobenius (ideal.quotient (ideal.span ({x} : set R)))
notation x `∣` y `in` R := (x : R) ∣ (y : R)
