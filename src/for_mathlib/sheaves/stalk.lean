/-
    Stalk (of types).

    https://stacks.math.columbia.edu/tag/0078

    Author: Ramon Fernandez Mir
-/

import for_mathlib.sheaves.opens
import topology.basic
import for_mathlib.sheaves.presheaf

universe u

section stalk

variables {α : Type u} [topological_space α]
variables (F : presheaf α) (x : α)

open topological_space

-- An element in the stalk is a pair (U, s) under an equivalence relation

structure stalk.elem :=
(U   : opens α)
(HxU : x ∈ U)
(s   : F U)

-- Equivalence relation on the set of pairs. (U,s) ~ (V,t) iff there exists W
-- open s.t. x ∈ W ⊆ U ∩ V, and s|W = t|W.

def stalk.relation : stalk.elem F x → stalk.elem F x → Prop :=
λ Us Vt,
    ∃ (W : opens α) (HxW : x ∈ W) (HWU : W ⊆ Us.U) (HWV : W ⊆ Vt.U),
    F.res Us.U W HWU Us.s = F.res Vt.U W HWV Vt.s

lemma stalk.relation.reflexive : reflexive (stalk.relation F x) :=
λ ⟨U, HxU, s⟩, ⟨U, HxU, set.subset.refl _, set.subset.refl _, rfl⟩

lemma stalk.relation.symmetric : symmetric (stalk.relation F x) :=
λ Us Vt ⟨W, HxW, HWU, HWV, Hres⟩, ⟨W, HxW, HWV, HWU, Hres.symm⟩

lemma stalk.relation.transitive : transitive (stalk.relation F x) :=
λ ⟨U, HxU, sU⟩ ⟨V, HxV, sV⟩ ⟨W, HxW, sW⟩,
λ ⟨R, HxR, HRU, HRV, HresR⟩ ⟨S, HxS, HSV, HSW, HresS⟩,
⟨R ∩ S, ⟨HxR, HxS⟩,
λ y ⟨HyR, _⟩, HRU HyR, λ y ⟨_, HyS⟩, HSW HyS,
have HURRS : _ := F.Hcomp U R (R ∩ S) (set.inter_subset_left _ _) HRU,
have HVRRS : _ := F.Hcomp V R (R ∩ S) (set.inter_subset_left _ _) HRV,
have HVSRS : _ := F.Hcomp V S (R ∩ S) (set.inter_subset_right _ _) HSV,
have HWSRS : _ := F.Hcomp W S (R ∩ S) (set.inter_subset_right _ _) HSW,
calc  F.res U (R ∩ S) _ sU
    = F.res R (R ∩ S) _ (F.res U R _ sU) : congr_fun HURRS sU
... = F.res R (R ∩ S) _ (F.res V R _ sV) : congr_arg _ HresR
... = F.res V (R ∩ S) _ sV               : congr_fun HVRRS.symm sV
... = F.res S (R ∩ S) _ (F.res V S _ sV) : congr_fun HVSRS sV
... = F.res S (R ∩ S) _ (F.res W S _ sW) : congr_arg _ HresS
... = F.res W (R ∩ S) _ sW               : congr_fun HWSRS.symm sW⟩

lemma stalk.relation.equivalence : equivalence (stalk.relation F x) :=
⟨stalk.relation.reflexive F x,
stalk.relation.symmetric F x,
stalk.relation.transitive F x⟩

instance stalk.setoid : setoid (stalk.elem F x) :=
{ r := stalk.relation F x,
  iseqv := stalk.relation.equivalence F x }

-- We define a stalk as the set of stalk elements under the defined relation.

definition stalk := quotient (stalk.setoid F x)

end stalk
