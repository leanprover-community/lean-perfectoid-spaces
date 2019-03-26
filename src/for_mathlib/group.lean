-- first lemma PR'ed, second one not yet.

import algebra.group data.equiv.basic
import group_theory.subgroup
import group_theory.quotient_group
import for_mathlib.equiv

variables {G : Type*} [group G]
open quotient_group

-- This one lemma in in PR #790
@[simp] lemma quotient_group.ker (N : set G) [normal_subgroup N] :
is_group_hom.ker (quotient_group.mk : G → quotient_group.quotient N) = N :=
begin
  ext g,
  rw [is_group_hom.mem_ker, eq_comm],
  show (((1 : G) : quotient_group.quotient N)) = g ↔ _,
  rw [quotient_group.eq, one_inv, one_mul],
end

-- this one lemma is not PR'ed yet.
def group_equiv.quot_eq_of_eq {G1 : set G} [normal_subgroup G1] {G2 : set G} [normal_subgroup G2]
(h : G1 = G2) : group_equiv (quotient G1) (quotient G2) :=
{ to_fun := λ q, quotient.lift_on' q (quotient_group.mk : G → quotient G2) $
    λ a b hab, quotient.sound'
  begin
    change a⁻¹ * b ∈ G1 at hab, rwa h at hab
  end,
  inv_fun := λ q, quotient.lift_on' q (quotient_group.mk : G → quotient G1) $
    λ a b hab, quotient.sound'
  begin
    change a⁻¹ * b ∈ G2 at hab, rwa ←h at hab,
  end,
  left_inv := λ x, by induction x; refl,
  right_inv := λ x, by induction x; refl,
  hom := ⟨λ a b, begin
    let f : G → quotient G2 := quotient_group.mk,
    have h2 := quotient_group.is_group_hom_quotient_lift G1 f,
    have h3 := h2 (λ x hx, by rwa [←is_group_hom.mem_ker f, quotient_group.ker G2, ←h]),
    have h4 := h3.mul,
    exact h4 a b,
  end⟩
  }
