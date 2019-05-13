import algebra.char_p
import ring_theory.ideals

def Prime := { p : ℕ // nat.prime p}
instance : has_coe Prime ℕ := ⟨subtype.val⟩
instance monoid.prime_pow {α : Type*} [monoid α]: has_pow α Prime := ⟨λ x p, x^p.val⟩


noncomputable def Frobenius (α : Type*) [semiring α] : α → α := λ x, x^(ring_char α)
notation `Frob` R `∕` x := Frobenius (ideal.quotient (ideal.span ({x} : set R)))
notation x `∣` y `in` R := (x : R) ∣ (y : R)
