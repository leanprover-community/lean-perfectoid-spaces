import ring_theory.ideal_operations -- PRs mostly go there

-- PR directly to ring_theory.ideals
lemma ideal.one_mem_of_unit_mem {R : Type*} [comm_ring R] {I : ideal R} {u : units R} (h : (u : R) ∈ I) :
(1 : R) ∈ I :=
begin
  have : (u : R)*(u⁻¹ : units R) ∈ I, from I.mul_mem_right h,
  rwa u.mul_inv at this
end

lemma ideal.span_singleton_mul {R : Type*} [comm_ring R] (x y : R) :
(ideal.span ({x} : set R)) * (ideal.span {y}) = ideal.span {x*y} :=
by simp [ideal.span_mul_span]

lemma ideal.span_singleton_pow {R : Type*} [comm_ring R] (x : R) (n : ℕ) :
(ideal.span ({x} : set R))^n = ideal.span {x^n} :=
begin
  induction n with n ih,
  { simp },
  { rw [pow_succ, ih, ideal.span_singleton_mul, pow_succ] }
end

lemma ideal.eq_bot_iff_zero {R : Type*} [comm_ring R] {I : ideal R} : I = ⊥ ↔ (I : set R) = {0} :=
begin
  split ; intro h,
  { simp [h] },
  { ext,
    change x ∈ (I : set R) ↔ _,
    simp [h] },
end

@[simp] lemma ideal.span_empty {R : Type*} [comm_ring R] : ideal.span (∅ : set R) = ⊥ :=
ideal.span_eq_bot.mpr (λ x h, false.elim h)

@[simp] lemma ideal.span_zero {R : Type*} [comm_ring R] : ideal.span ({0} : set R) = ⊥ :=
ideal.span_eq_bot.mpr $ λ x, set.mem_singleton_iff.mp
