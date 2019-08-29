import algebra.char_p
import for_mathlib.primes

noncomputable def Frobenius (α : Type*) [semiring α] : α → α := λ x, x^(ring_char α)
notation `Frob` R `∕` x := Frobenius (ideal.quotient (ideal.span ({x} : set R)))
notation x `∣` y `in` R := (x : R) ∣ (y : R)
