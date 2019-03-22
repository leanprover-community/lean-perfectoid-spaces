import group_theory.quotient_group
import for_mathlib.group

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

-- I don't use this any more, first because group_equiv.quotient is more general
-- and second because I don't like the definition of the function via quotient_group.map
def group_equiv.quotient' {G : Type*} {H : Type*} [group G] [group H]
(h : group_equiv G H) (K : set H) [normal_subgroup K] :
group_equiv (quotient_group.quotient (h.to_equiv ⁻¹' K)) (quotient_group.quotient K) :=
{ to_fun := map (h.to_equiv ⁻¹' K) K h.to_fun (le_refl (h.to_equiv ⁻¹' K)),
  inv_fun := map K (h.to_equiv ⁻¹' K) h.symm.to_fun (λ x H, show h.to_fun (h.inv_fun x) ∈ K, by rwa h.right_inv x),
  left_inv := λ g, begin
    rw quotient_group.map_comp,
    convert map_id _ g,
    ext x, exact h.left_inv x
  end,
  right_inv := λ g, begin
    rw quotient_group.map_comp,
    convert map_id _ g,
    ext x, exact h.right_inv x
  end,
  mul_hom := begin
    have H : is_group_hom (map (h.to_equiv ⁻¹' K) K h.to_fun (le_refl (h.to_equiv ⁻¹' K))) :=
    by apply_instance,
    cases H with H, exact H,
  end}

lemma quotient_group.ker_mk {G : Type*} [group G] (N : set G) [normal_subgroup N] :
  is_group_hom.ker (quotient_group.mk : G → quotient_group.quotient N) = N :=
begin
  ext g,
  show quotient.mk' g ∈ {(1 : quotient_group.quotient N)} ↔ g ∈ N,
  rw set.mem_singleton_iff,
  show _ = quotient.mk' (1 : G) ↔ _,
  rw quotient.eq',
  show g⁻¹ * 1 ∈ N ↔ _,
  rw [mul_one, is_subgroup.inv_mem_iff],
end

-- This version is better, but Mario points out that really I shuold be using a
-- relation rather than h2 : he.to_equiv ⁻¹' K = J.
def group_equiv.quotient {G : Type*} {H : Type*} [group G] [group H]
  (he : group_equiv G H) (J : set G) [normal_subgroup J] (K : set H) [normal_subgroup K]
  (h2 : he.to_equiv ⁻¹' K = J) :
group_equiv (quotient_group.quotient J) (quotient_group.quotient K) :=
{ to_fun := quotient_group.lift J (λ g, quotient_group.mk (he.to_equiv g)) begin
    unfold set.preimage at h2,
    intros g hg,
    rw ←h2 at hg,
    rw ←is_group_hom.mem_ker (quotient_group.mk : H → quotient_group.quotient K),
    rwa quotient_group.ker_mk,
  end,
  inv_fun := quotient_group.lift K (λ h, quotient_group.mk (he.symm.to_equiv h)) begin
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
  mul_hom := begin
    have H := quotient_group.is_group_hom_quotient_lift J _ _,
    cases H with H,
    exact H, -- !
  end
  }
