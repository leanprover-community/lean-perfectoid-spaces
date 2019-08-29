import algebra.group data.equiv.basic
import group_theory.subgroup
import group_theory.quotient_group
import for_mathlib.equiv

variables {G : Type*} [group G]
open quotient_group

-- this one lemma is not PR'ed yet.
def mul_equiv.quot_eq_of_eq {G1 : set G} [normal_subgroup G1] {G2 : set G} [normal_subgroup G2]
(h : G1 = G2) : mul_equiv (quotient G1) (quotient G2) :=
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
  map_mul' := λ a b, begin
    let f : G → quotient G2 := quotient_group.mk,
    have h2 := quotient_group.is_group_hom_quotient_lift G1 f,
    have h3 := h2 (λ x hx, by rwa [←is_group_hom.mem_ker f, quotient_group.ker_mk G2, ←h]),
    have h4 := h3.map_mul,
    exact h4 a b,
  end
  }

variables {M : Type*} [monoid M]

lemma units.ext_inv (a b : units M) (h : a.inv = b.inv) : a = b :=
inv_inj $ units.ext h

-- is this true for non-commutative monoids?
-- KL: No, s := nat.pred, t := nat.succ, u := id
/-- produces a unit s from a proof that s divides a unit -/
def units.unit_of_mul_left_eq_unit {M : Type*} [comm_monoid M]
  {s t : M} {u : units M}
(h : s * t = u) : units M :=
{ val := s,
  inv := t * (u⁻¹ : units M),
  val_inv := by {show s * (t * (u⁻¹ : units M)) = 1, rw [←mul_assoc, h], simp},
  inv_val := by {show t * (u⁻¹ : units M) * s = 1, rw [mul_comm, ←mul_assoc, h], simp} }
