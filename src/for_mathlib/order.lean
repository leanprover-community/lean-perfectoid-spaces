import algebra.order order.basic

variables {α : Type*} {β : Type*} [decidable_linear_order α] [decidable_linear_order β]
variables {f : α → β}

lemma monotone.map_max (hf : monotone f) {a b : α} :
  f (max a b) = max (f a) (f b) :=
begin
  by_cases h : a ≤ b,
  { rw [max_eq_right h, max_eq_right (hf h)] },
  { rw not_le at h, replace h := le_of_lt h,
    rw [max_eq_left h, max_eq_left (hf h)] },
end
