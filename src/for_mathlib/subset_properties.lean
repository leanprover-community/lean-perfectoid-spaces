
import topology.subset_properties
import for_mathlib.open_embeddings

namespace topological_space

-- is_irreducible_closure is currently in the root namespace.
--#print is_irreducible_closure
--#check @is_irreducible_closure

variables {X : Type*} [topological_space X]

lemma irreducible_closure_iff (S : set X) :
  is_irreducible (closure S) ↔ is_irreducible S :=
begin
  split, swap, exact is_irreducible_closure,
  rintros hS U V hU hV ⟨x, hx⟩ ⟨y, hy⟩,
  cases (hS U V hU hV _ _) with z hz, swap, use [x, ⟨subset_closure hx.1, hx.2⟩],
    swap, use [y, ⟨subset_closure hy.1, hy.2⟩],
  rcases set.ne_empty_iff_exists_mem.1 (mem_closure_iff.1 hz.1 (U ∩ V)
    (is_open_inter _ _ _ hU hV) hz.2) with ⟨w, hUV, hS⟩,
  use ⟨w, hS, hUV⟩,
end

lemma irred_closure_singleton (x : X) :
  is_irreducible (closure {x} : set X) :=
by {rw irreducible_closure_iff, exact is_irreducible_singleton}

/-
Remark 3.4. Let X be a topological space. If U ⊆ X is an open subset and Z ⊆ X
is irreducible and closed, Z ∩ U is open in Z. Hence if Z ∩ U 6 = ∅, then Z ∩ U is an
irreducible closed subset of U whose closure in X is Z. Together with Lemma 3.2 this
shows that there are mutually inverse bijective maps
{Y ⊆ U irreducible closed} ↔ {Z ⊆ X irreducible closed with Z ∩ U 6 = ∅}
(3.4.1)
Y 7→ Y
(closure in X)
Z ∩ U ←7 Z
-/

example {X : Type*} [topological_space X] {U : Type*} [topological_space U] {f : X → U} :

def irred_closed_in_open (U Z : set X) (hU : _root_.is_open U) (hZ : _root_.is_closed Z) :
{Y : set X // Π (h : Y ⊆ U), is_irreducible Y ∧ is_closed (@set.univ U : set U)}


end topological_space -- namespace
