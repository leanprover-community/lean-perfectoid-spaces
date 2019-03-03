import group_theory.quotient_group
import for_mathlib.group

-- Some stuff is now in mathlib

namespace quotient_group

theorem map_id {G : Type*} [group G] (K : set G) [normal_subgroup K] (g : quotient K) :
map K K id (λ x h, h) g = g := by induction g; refl

theorem quotient_group.map_comp
  {G : Type*} {H : Type*} {J : Type*}
  [group G] [group H] [group J]
  (a : G → H) [is_group_hom a] (b : H → J) [is_group_hom b]
  {G1 : set G} {H1 : set H} {J1 : set J}
  [normal_subgroup G1] [normal_subgroup H1] [normal_subgroup J1]
  (h1 : G1 ⊆ a ⁻¹' H1) (h2 : H1 ⊆ b ⁻¹' J1)
  (g : quotient G1) :
map H1 J1 b h2 (map G1 H1 a h1 g) = map G1 J1 (b ∘ a) (λ _ hx, h2 $ h1 hx) g :=
by induction g; refl

theorem group_equiv.quotient {G : Type*} {H : Type*} [group G] [group H]
(h : group_equiv G H) (K : set H) [normal_subgroup K] :
group_equiv (quotient_group.quotient (h ⁻¹' K)) (quotient_group.quotient K) :=
{ to_fun := map (h ⁻¹' K) K h (le_refl (h ⁻¹' K)),
  inv_fun := map K (h ⁻¹' K) h.symm (λ x H, show h.to_fun (h.inv_fun x) ∈ K, by rwa h.right_inv x),
  left_inv := λ g, begin
    rw quotient_group.map_comp,
    convert map_id _ g,
    ext x, exact h.left_inv x,
  end,
  right_inv := λ g, begin
    rw quotient_group.map_comp,
    convert map_id _ g,
    ext x, exact h.right_inv x
  end,
  hom := by apply_instance }

end quotient_group
