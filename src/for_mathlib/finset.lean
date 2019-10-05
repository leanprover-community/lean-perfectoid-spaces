import data.finset

lemma finset.fold_max_lt {α : Type*} {β : Type*} [decidable_eq α] [decidable_linear_order β]
  (s : finset α) (f : α → β) (b x : β) :
  s.fold max b f < x ↔ (b < x ∧ ∀ a∈s, f a < x) :=
begin
  apply finset.induction_on s, { simp, },
  clear s, intros a s ha IH,
  rw [finset.fold_insert ha, max_lt_iff, IH, ← and_assoc, and_comm (f a < x), and_assoc],
  apply and_congr iff.rfl,
  split,
  { rintro ⟨h₁, h₂⟩, intros b hb, rw finset.mem_insert at hb,
    rcases hb with rfl|hb; solve_by_elim },
  { intro h, split,
    { exact h a (finset.mem_insert_self _ _), },
    { intros b hb, apply h b, rw finset.mem_insert, right, exact hb } }
end

