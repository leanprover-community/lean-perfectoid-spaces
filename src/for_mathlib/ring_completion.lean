import tactic.ring
import for_mathlib.topological_structures
import for_mathlib.group_completion

noncomputable theory

open filter uniform_space function

section topological_ring
universe u
variables {A : Type u} [topological_space A] [comm_ring A] [topological_ring A]

def uncurry_mul : completion A × completion A → completion A := completion.map₂ (*)

instance completion_mul : has_mul (completion A) := ⟨curry (uncurry_mul)⟩

instance : ring (completion A) :=
begin
  refine_struct {
    one := ((1 : A) : completion A),
    mul := (*),
    ..completion_group_str},
  repeat { sorry }
end

instance : uniform_space (completion A) := topological_add_group.to_uniform_space (completion A)

instance completion_ring_top : topological_ring (completion A) :=
sorry

variables {B : Type u} [topological_space B] [comm_ring B] [topological_ring B]

instance completion_map_ring_hom {f : A → B} [is_add_group_hom f] (h : continuous f) :
  is_ring_hom (completion.map f) := sorry

end topological_ring