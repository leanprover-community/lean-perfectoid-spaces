import data.equiv.algebra
import group_theory.quotient_group

-- Some stuff is now in mathlib

namespace quotient_group

theorem map_id {G : Type*} [group G] (K : set G) [normal_subgroup K] (g : quotient K) :
map K K id (λ x h, h) g = g := by induction g; refl

theorem map_comp
  {G : Type*} {H : Type*} {J : Type*}
  [group G] [group H] [group J]
  (a : G → H) [is_group_hom a] (b : H → J) [is_group_hom b]
  {G1 : set G} {H1 : set H} {J1 : set J}
  [normal_subgroup G1] [normal_subgroup H1] [normal_subgroup J1]
  (h1 : G1 ⊆ a ⁻¹' H1) (h2 : H1 ⊆ b ⁻¹' J1)
  (g : quotient G1) :
map H1 J1 b h2 (map G1 H1 a h1 g) = map G1 J1 (b ∘ a) (λ _ hx, h2 $ h1 hx) g :=
by induction g; refl

end quotient_group

open quotient_group

-- This version is better (than a previous, deleted version),
-- but Mario points out that really I shuold be using a
-- relation rather than h2 : he.to_equiv ⁻¹' K = J.
def mul_equiv.quotient {G : Type*} {H : Type*} [group G] [group H]
  (he : G ≃* H) (J : set G) [normal_subgroup J] (K : set H) [normal_subgroup K]
  (h2 : he.to_equiv ⁻¹' K = J) :
mul_equiv (quotient_group.quotient J) (quotient_group.quotient K) :=
{ to_fun := quotient_group.lift J (mk ∘ he) begin
    unfold set.preimage at h2,
    intros g hg,
    rw ←h2 at hg,
    rw ←is_group_hom.mem_ker (quotient_group.mk : H → quotient_group.quotient K),
    rwa quotient_group.ker_mk,
  end,
  inv_fun := quotient_group.lift K (mk ∘ he.symm) begin
    intros h hh,
    rw ←is_group_hom.mem_ker (quotient_group.mk : G → quotient_group.quotient J),
    rw quotient_group.ker_mk,
    show he.to_equiv.symm h ∈ J,
    rw ←h2,
    show he.to_equiv (he.to_equiv.symm h) ∈ K,
    convert hh,
    exact he.to_equiv.right_inv h
  end,
  left_inv := λ g, begin
    induction g,
    conv begin
      to_rhs,
      rw ←he.to_equiv.left_inv g,
    end,
    refl, refl,
    end,
  right_inv := λ h, begin
    induction h,
    conv begin
      to_rhs,
      rw ←he.to_equiv.right_inv h,
    end,
    refl, refl,
  end,
  map_mul' := (quotient_group.is_group_hom_quotient_lift J _ _).map_mul }
