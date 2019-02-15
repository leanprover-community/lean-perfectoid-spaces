import data.subtype

universe u

@[simp] lemma val_prop {X : Type u} {S : set X} (x : {x // x ∈ S}) : x.val ∈ S := x.property
