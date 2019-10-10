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

variables (R : Type*) (A : Type*) [comm_ring R] [comm_ring A] [algebra R A] (p : nat.primes)

lemma ring_char.eq_iff (n : ℕ) :
  ring_char R = n ↔ char_p R n :=
begin
  split,
  { rintro rfl, exact ring_char.char R },
  { intro h, exact (ring_char.eq R h).symm }
end

def char_p.zmodp_algebra [hp : char_p R p] : algebra (zmodp p p.2) R :=
algebra.of_ring_hom zmod.cast (@zmod.cast_is_ring_hom R _ ⟨p,_⟩ hp)

instance zmod.char_p (n : ℕ+) : char_p (zmod n) n :=
⟨λ k, zmod.eq_zero_iff_dvd_nat⟩

instance zmodp.char_p (p : ℕ) (hp : p.prime) : char_p (zmodp p hp) p :=
zmod.char_p ⟨p, _⟩

lemma char_p_algebra [hp : char_p R p] (h : (0:A) ≠ 1) : char_p A p :=
begin
  letI := char_p.zmodp_algebra R,
  letI : nonzero_comm_ring (algebra.comap (zmodp p p.2) R A) :=
  { zero_ne_one := h, .. ‹comm_ring A› },
  change char_p (algebra.comap (zmodp p p.2) R A) p,
  convert char_p_algebra_over_field (zmodp p p.2),
  { exact algebra.comap.algebra _ _ _ },
  { apply_instance }
end

lemma Frob_mod_surjective_char_p [hp : char_p R p] (h : surjective (Frobenius R)) :
  surjective (Frob R∕p) :=
begin
  rintro ⟨x⟩,
  rcases h x with ⟨y, rfl⟩,
  refine ⟨ideal.quotient.mk _ y, _⟩,
  delta Frobenius,
  rw ← ideal.quotient.mk_pow,
  congr' 2,
  rw [char_p.eq R (ring_char.char R) hp, ring_char.eq_iff],
  refine @char_p_algebra R _ _ _
    (algebra.of_ring_hom (ideal.quotient.mk _) (ideal.quotient.is_ring_hom_mk _)) _ hp _,
  assume H, apply p.not_dvd_one,
  rw [eq_comm, ← ideal.quotient.mk_one, ideal.quotient.eq_zero_iff_mem,
      ideal.mem_span_singleton] at H,
  rw [show (p : R) = (p : ℕ), by rw coe_coe] at H,
  rwa [char_p.cast_eq_zero R, zero_dvd_iff,
    ← nat.cast_one, char_p.cast_eq_zero_iff R p] at H,
end

end
