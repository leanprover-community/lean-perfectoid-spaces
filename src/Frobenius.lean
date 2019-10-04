import algebra.char_p
import for_mathlib.primes

/-!
The main purpose of this file is to introduce notation that
is not available in mathlib, and that we don't want to set up in the main file.
-/

/--The Frobenius endomorphism of a semiring-/
noncomputable def Frobenius (α : Type*) [semiring α] : α → α := λ x, x^(ring_char α)

notation `Frob` R `∕` x := Frobenius (ideal.quotient (ideal.span ({x} : set R)))

notation x `∣` y `in` R := (x : R) ∣ (y : R)






