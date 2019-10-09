import algebra.char_p
import for_mathlib.primes
import for_mathlib.char_p
import for_mathlib.ideal_operations

/-!
The main purpose of this file is to introduce notation that
is not available in mathlib, and that we don't want to set up in the main file.
-/

/--The Frobenius endomorphism of a semiring-/
noncomputable def Frobenius (α : Type*) [semiring α] : α → α := λ x, x^(ring_char α)

notation `Frob` R `∕` x := Frobenius (ideal.quotient (ideal.span ({x} : set R)))

notation x `∣` y `in` R := (x : R) ∣ (y : R)

section
open function

variables (R : Type*) [comm_ring R] (p : nat.primes)
lemma Frob_mod_surjective_char_p (h : surjective (Frobenius R)) (hp : ring_char R = p) :
  surjective (Frob R∕p) :=
begin
  rintro ⟨x⟩,
  rcases h x with ⟨y, rfl⟩,
  refine ⟨ideal.quotient.mk _ y, _⟩,
  delta Frobenius,
  rw ← ideal.quotient.mk_pow,
  congr' 2,
  haveI : char_p R p := by { rw ← hp, apply_instance },
  rw [show (p : R) = (p : ℕ), by rw coe_coe],
  rw [char_p.cast_eq_zero, ideal.span_zero],
  sorry
end

end
