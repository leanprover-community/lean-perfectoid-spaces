universes u v

open function

theorem option.map_inj
  {α : Type u} {β : Type v} {f : α → β} (Hf : injective f) :
  injective (option.map f)
| none      none      H := rfl
| (some a₁) (some a₂) H := by rw Hf (option.some.inj H)
