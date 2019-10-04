import ring_theory.polynomial

namespace polynomial

variables {R : Type*} [comm_ring R]

lemma monic.as_sum {f : polynomial R} (hf : f.monic) :
  f = X^(f.nat_degree) + ((finset.range f.nat_degree).sum $ λ i, C (f.coeff i) * X^i) :=
begin
  ext n,
  rw [coeff_add, coeff_X_pow],
  rw show coeff (finset.sum (finset.range (nat_degree f)) (λ (i : ℕ), C (coeff f i) * X ^ i)) n =
    (finset.sum (finset.range (nat_degree f)) (λ (i : ℕ), coeff (C (coeff f i) * X ^ i) n)),
  { symmetry,
    let tmp : _ := _,
    refine @finset.sum_hom _ _ _ _ _ _ _ (λ f, coeff f n) tmp,
    exact { map_add := λ f g, coeff_add f g n, map_zero := rfl }, },
  split_ifs with h,
  { subst h, convert (add_zero _).symm, { symmetry, exact hf },
    apply finset.sum_eq_zero,
    intros i hi, rw finset.mem_range at hi, replace hi := ne_of_gt hi,
    simp [hi], },
  { rw zero_add,
    by_cases hn : n < nat_degree f,
    { rw finset.sum_eq_single n, { simp, },
      { intros i hi hin, simp [hin.symm], },
      { rw finset.mem_range, intro H, contradiction, } },
    { push_neg at hn, replace hn := lt_of_le_of_ne hn h.symm,
      rw [finset.sum_eq_zero, coeff_eq_zero_of_degree_lt],
      { refine lt_of_le_of_lt degree_le_nat_degree _, rwa with_bot.coe_lt_coe },
      { intros i hi, rw finset.mem_range at hi, have : n ≠ i, by linarith, simp [this], } } }
end

end polynomial

