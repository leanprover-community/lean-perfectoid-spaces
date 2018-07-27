import group_theory.coset 

-- for images
import data.set.basic

-- finsupp for free abelian groups
import data.finsupp 

universes u v 

variables (G : Type u) [group G] (H : Type v) [group H] (S : set G)

-- maybe use group.in_closure?
theorem closure_image (f : G → H) [is_group_hom f] : 
f '' (group.closure (is_group_hom.ker f) ∪ S) = group.closure (f '' S) := sorry 

-- don't know why we need decidable equality -- maybe some finsupp reason
example (X : Type u) [decidable_eq X] : add_comm_group (X →₀ ℤ) := by apply_instance

definition group.free_ab_gens (X : Type u) [decidable_eq X] : 
X → (X →₀ ℤ) := λ x, finsupp.single x (1 : ℤ)

#check @group.closure 

-- do we have to copy out all of the definitions here?
definition group.add_closure {G : Type u} [add_group G] (S : set G) : set G := sorry 

-- maybe use finsupp.induction?
theorem closure_free_gens (X : Type u) [decidable_eq X] : 
group.add_closure ((group.free_ab_gens X) '' set.univ) = set.univ := sorry 
