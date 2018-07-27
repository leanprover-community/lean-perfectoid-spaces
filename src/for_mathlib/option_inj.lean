universes u v 

open function

theorem option.map_inj
  {α : Type u} {β : Type v} {f : α → β} (Hf : injective f) :
injective (option.map f) := λ a₁ a₂ H,
begin
  cases h₁ : a₁;cases h₂ : a₂;rw [h₁,h₂] at H; try {exact option.no_confusion H},
  congr,apply Hf,apply option.some.inj,exact H
end 
