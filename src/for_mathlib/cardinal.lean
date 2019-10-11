import set_theory.cardinal

lemma cardinal.eq_one_iff_nonempty_subsingleton {α : Type*} :
  cardinal.mk α = 1 ↔ (nonempty α ∧ subsingleton α) :=
by rw [← cardinal.ne_zero_iff_nonempty, ← cardinal.le_one_iff_subsingleton,
  eq_iff_le_not_lt, ← cardinal.succ_zero, cardinal.lt_succ, cardinal.le_zero, and_comm]
