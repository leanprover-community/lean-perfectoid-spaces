universes u v

open function

-- PR'd as #978, `option.injective_map`.
theorem option.map_inj
  {α : Type u} {β : Type v} {f : α → β} (Hf : injective f) :
  injective (option.map f)
| none      none      H := rfl
| (some a₁) (some a₂) H := by rw Hf (option.some.inj H)
