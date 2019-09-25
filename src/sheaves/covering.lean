/-
  Package the definition of an open cover of an open set.

  Author: Ramon Fernandez Mir
-/

import topology.basic
import topology.opens
import sheaves.opens

universes u

open topological_space lattice

section covering

variables {α : Type u} [topological_space α]

-- Open cover.

structure covering (U : opens α) :=
{γ    : Type u}
(Uis  : γ → opens α)
(Hcov : ⋃ Uis = U)

variable (α)

def covering.univ := covering (@opens.univ α _)

variable {α}

-- If ⋃ Ui = U then for all i, Ui ⊆ U.

lemma subset_covering {U : opens α} {OC : covering U} :
∀ i, OC.Uis i ⊆ U :=
λ i x Hx, OC.Hcov ▸ opens_supr_mem OC.Uis i x Hx

-- Make covering from standard definition. Used for instance in compactness.

def opens.from_sets {A : Type*} [topological_space A]
: set (set A) → set (opens A) := λ C, { x | x.1 ∈ C }

lemma opens.from_sets.eq {A : Type*} [topological_space A]
(S : set (set A)) (HS : ∀ (t : set A), t ∈ S → is_open t)
: subtype.val '' (opens.from_sets S) = S :=
set.ext $ λ x, ⟨
  λ ⟨x', Hx', Hval⟩, Hval ▸ Hx',
  λ Hx, by simp [HS x Hx]; by exact Hx⟩

@[reducible] def covering.from_cover {A : Type*} [topological_space A]
(U     : opens A)
(C     : set (set A))
(HC    : ∀ (t : set A), t ∈ C → is_open t)
(Hcov : U.1 = ⋃₀ C)
: covering U :=
{ γ := opens.from_sets C,
  Uis := λ x, x,
  Hcov :=
    begin
      apply subtype.ext.2,
      rw Hcov,
      apply set.ext,
      intros x,
      split,
      { intros Hx,
        rcases Hx with ⟨U, HU, HxU⟩,
        existsi U,
        simp at HU,
        rcases HU with ⟨OU, HU⟩,
        rw ←opens.from_sets.eq C HC,
        split,
        { simp [HU],
          use OU, },
        { exact HxU, } },
      { intros Hx,
        rcases Hx with ⟨U, HU, HxU⟩,
        use U,
        simp,
        use (HC U HU),
        { simp [opens.from_sets],
          exact HU, },
        { exact HxU, }  }
    end, }

lemma covering.from_cover.Uis {A : Type*} [topological_space A]
(U     : opens A)
(C     : set (set A))
(HC    : ∀ (t : set A), t ∈ C → is_open t)
(Hcov : U.1 = ⋃₀ C)
: ∀ i, ((covering.from_cover U C HC Hcov).Uis i).1 ∈ C :=
begin
  intros i,
  simp [covering.from_cover] at *,
  cases i with i Hi,
  simp,
  simp [opens.from_sets] at *,
  exact Hi,
end

end covering
