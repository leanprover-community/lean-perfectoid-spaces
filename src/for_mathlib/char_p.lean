import algebra.char_p
import ring_theory.algebra
import ring_theory.ideal_operations
import ring_theory.principal_ideal_domain

open function

lemma map_nat_cast {α : Type*} {β : Type*} [semiring α] [semiring β]
  (f : α → β) [is_semiring_hom f] (n : ℕ) :
  f n = n :=
begin
  induction n with n ih, { exact is_semiring_hom.map_zero f },
  rw [nat.cast_succ, nat.cast_succ, is_semiring_hom.map_add f, ih, is_semiring_hom.map_one f],
end


section
variables (p : nat.primes) (R : Type*) [semiring R] [char_p R p]
include p

lemma ring_char.prime : nat.prime (ring_char R) :=
by { rw ← ring_char.eq R ‹_›, exact p.2 }

end

instance ring_char.char (R : Type*) [semiring R] : char_p R (ring_char R) :=
{ cast_eq_zero_iff := ring_char.spec R }

section
variables {K : Type*} {R : Type*} {p : ℕ} [discrete_field K] [nonzero_comm_ring R] [algebra K R]

-- is_field_hom.injective is not general enough
lemma hom_injective (f : K → R) [is_ring_hom f] : injective f :=
begin
  apply (is_ring_hom.inj_iff_ker_eq_bot f).mpr,
  apply classical.or_iff_not_imp_right.mp (ideal.eq_bot_or_top _),
  rw ideal.eq_top_iff_one,
  exact is_ring_hom.not_one_mem_ker f,
end

variable (K)

lemma char_p_algebra_over_field [char_p K p] : char_p R p :=
{ cast_eq_zero_iff := λ n,
  begin
    have : injective (algebra_map R : K → R) := hom_injective _,
    rw [← char_p.cast_eq_zero_iff K, ← this.eq_iff, algebra.map_zero,
      map_nat_cast (algebra_map R : K → R)],
  end }
end

section char_p_subring
open int
variables {R : Type*} [comm_ring R]

lemma nat.eq_of_dvd {p q : ℕ} (h : p ∣ q) (h' : q ∣ p) : p = q :=
begin
  cases h with n hn,
  cases h' with m hm,
  cases nat.eq_zero_or_pos p,
    simp [h, hn],
  rw [hn, mul_assoc, eq_comm, nat.mul_right_eq_self_iff h, nat.mul_eq_one_iff] at hm,
  simp [hn, hm.1],
end

lemma int.nat_abs_dvd_iff {p : ℤ} {n : ℕ} : nat_abs p ∣ n ↔ p ∣ n :=
begin
  split; intro h,
    refine dvd_trans _ (coe_nat_dvd.mpr h), rw dvd_nat_abs,
  rw ←coe_nat_dvd,
  refine dvd_trans _ h,
  rw nat_abs_dvd,
end

lemma cast_nat_abs_zero (k : ℤ) (h : (k : R) = 0) :  (nat_abs k : R) = 0 :=
begin
  cases nat_abs_eq k with hpos hneg,
    show (((nat_abs k) : ℤ) : R) = 0,
    rwa ←hpos,
  show (((nat_abs k) : ℤ) : R) = 0,
  rw eq_neg_of_eq_neg hneg,
  simp [h],
end

variables {S : Type*} [comm_ring S] {φ : R → S} [is_ring_hom φ]

lemma int.cast_ump : (int.cast : ℤ → S) = φ ∘ (int.cast : ℤ → R) :=
begin
  ext k,
  induction k using int.induction_on with k ih k ih,
  { simp,
    change ((0 : ℤ) : S) = φ ((0 : ℤ) : R),
    rw [int.cast_zero, int.cast_zero, is_ring_hom.map_zero φ] },
  { rw [is_ring_hom.map_add (int.cast : ℤ → S), ih,
        is_ring_hom.map_add (φ ∘ (int.cast : ℤ → R)),
        is_ring_hom.map_one (φ ∘ (int.cast : ℤ → R))],
    simp,
    exact int.cast_one },
  { rw [is_ring_hom.map_sub (int.cast : ℤ → S), ih,
        is_ring_hom.map_sub (φ ∘ (int.cast : ℤ → R)),
        is_ring_hom.map_one (φ ∘ (int.cast : ℤ → R))],
    simp,
    exact int.cast_one }
end

variables {T : Type*} [comm_ring T] {ψ : S → T} [is_ring_hom ψ]
open is_ring_hom

lemma is_ring_hom.ker_eq_of_inj (h : injective ψ) : ker (ψ ∘ φ) = ker φ :=
begin
  ext x,
  rw [mem_ker, mem_ker, comp_app, ←map_zero ψ],
  exact ⟨λ H, h H, congr_arg ψ⟩
end

open ideal.is_principal

lemma char_is_char : ring_char R = nat_abs (generator (is_ring_hom.ker (int.cast : ℤ → R))) :=
begin
  apply nat.eq_of_dvd,
  { rw ← ring_char.spec R,
    apply cast_nat_abs_zero,
    have := generator_mem (is_ring_hom.ker (int.cast : ℤ → R)),
    rwa is_ring_hom.mem_ker at this
  },
  { rw [int.nat_abs_dvd_iff, ← mem_iff_generator_dvd, is_ring_hom.mem_ker],
    apply char_p.cast_eq_zero }
end

lemma subring_ring_char (h : injective φ) : ring_char R = ring_char S :=
begin
  rw [char_is_char, char_is_char],
  suffices : is_ring_hom.ker (int.cast : ℤ → R) = is_ring_hom.ker (int.cast : ℤ → S), by rw this,
  have : (int.cast : ℤ → S) = φ ∘ (int.cast : ℤ → R), from int.cast_ump,
  simp only [this],
  exact (is_ring_hom.ker_eq_of_inj h).symm
end

lemma char_p_ring_char (p : nat.primes) : char_p R p ↔ ring_char R = p :=
⟨λ h, (ring_char.eq R h).symm, λ h, h ▸ (classical.some_spec (char_p.exists_unique R)).1⟩

lemma subring_char_p (p : nat.primes) (h : injective φ) : char_p S p ↔ char_p R p :=
begin
  repeat { rw char_p_ring_char },
  rwa subring_ring_char h
end

end char_p_subring
