import topology.opens
import category_theory.functor

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
{f : α → β}

open topological_space

def is_open_map.map (h : is_open_map f) : opens α → opens β :=
λ U, ⟨f '' U.1, h U.1 U.2⟩

def functor.is_open_map.map (h : is_open_map f) : opens α ⥤ opens β :=
{ obj := is_open_map.map h,
  map := λ X Y hXY, begin cases hXY, cases hXY, apply ulift.up, apply plift.up,
    rintros x ⟨a, ha, ha'⟩, rw ←ha', use a, exact ⟨hXY ha, rfl⟩ end,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }
