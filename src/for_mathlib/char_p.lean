import algebra.char_p
import ring_theory.algebra
import ring_theory.ideal_operations

lemma map_nat_cast {α : Type*} {β : Type*} [semiring α] [semiring β]
  (f : α → β) [is_semiring_hom f] (n : ℕ) :
  f n = n :=
begin
  induction n with n ih, { exact is_semiring_hom.map_zero f },
  rw [nat.cast_succ, nat.cast_succ, is_semiring_hom.map_add f, ih, is_semiring_hom.map_one f],
end

open function
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

lemma char_p_algebra [char_p K p] : char_p R p :=
{ cast_eq_zero_iff := λ n,
  begin
    have : injective (algebra_map R : K → R) := hom_injective _,
    rw [← char_p.cast_eq_zero_iff K, ← this.eq_iff, algebra.map_zero,
      map_nat_cast (algebra_map R : K → R)],
  end }
