import topology.opens
import category_theory.functor

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
{f : α → β}

open topological_space

def topological_space.is_open_map_map (h : is_open_map f) : opens α → opens β :=
λ U, ⟨f '' U.1, h U.1 U.2⟩

def functor.is_open_map.map (h : is_open_map f) : opens α ⥤ opens β :=
{ obj := topological_space.is_open_map_map h,
  map := λ X Y hXY, ⟨⟨set.mono_image  hXY.1.1⟩⟩,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

def continuous.comap {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {f : X → Y} (hf : continuous f) (V : opens Y) : opens X := ⟨f ⁻¹' V.1, hf V.1 V.2⟩

def continuous.comap_id {X : Type*} [topological_space X] (U : opens X) :
continuous.comap (continuous_id) U = U := by ext; refl

def continuous.comap_mono {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {f : X → Y} (hf : continuous f) {V W : opens Y} (hVW : V ⊆ W) : hf.comap V ⊆ hf.comap W :=
λ _ h, hVW h
