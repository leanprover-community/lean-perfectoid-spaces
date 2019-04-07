import tactic.abel

import topology.algebra.group
--import topology.algebra.uniform_ring
import for_mathlib.uniform_space.ring
import ring_theory.subring

import for_mathlib.topology
import for_mathlib.filter

universes u v
open filter set

section
variables {G : Type u} [add_comm_group G]

def prod_map {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}
  (f : α₁ → α₂) (g : β₁ → β₂) : α₁ × β₁ → α₂ × β₂
:= λ p, (f p.1, g p.2)

infix `⨯`:90 := prod_map

def add_group_with_zero_nhd.of_open_add_subgroup
  (H : set G) [is_add_subgroup H] (t : topological_space H) (h : @topological_add_group H t _) :
  add_group_with_zero_nhd G :=
{ Z := (nhds (0 : H)).map $ (subtype.val : H → G),
  zero_Z := calc pure ((0 : H) : G) = map subtype.val (pure 0) : (filter.map_pure _ _).symm
                                ... ≤ _ : map_mono (pure_le_nhds _),
  sub_Z :=
  begin
    let δ_G := λ (p : G × G), p.1 - p.2,
    let δ_H := λ (p : H × H), p.1 - p.2,
    let ι : H → G := subtype.val,
    let N := nhds (0 : H),
    let Z := map subtype.val N,
    change map δ_G (filter.prod Z Z) ≤ Z,
    have key₁: map δ_H (nhds (0, 0)) ≤ N,
    { rw [show N = nhds (δ_H (0, 0)), by simp [*]],
      exact continuous_sub'.tendsto _ },
    have key₂ : δ_G ∘ ι⨯ι = ι ∘ δ_H,
    { ext p,
      change (p.1 : G) - (p.2 : G) = (p.1 - p.2 : G),
      simp [is_add_subgroup.coe_neg, is_add_submonoid.coe_add] },

    calc map δ_G (filter.prod Z Z)
          = map δ_G (map (ι ⨯ ι) $ filter.prod N N) : by rw prod_map_map_eq;refl
      ... = map ι (map δ_H $ filter.prod N N)       : map_comm key₂ _
      ... = map ι (map δ_H $ nhds (0, 0))           : by rw ← nhds_prod_eq
      ... ≤ map ι N : map_mono key₁
  end,
  ..‹add_comm_group G› }

def of_open_add_subgroup {G : Type u} [str : add_comm_group G] (H : set G) [is_add_subgroup H]
  (t : topological_space H) (h : @topological_add_group H t _) : topological_space G :=
@add_group_with_zero_nhd.topological_space G
  (add_group_with_zero_nhd.of_open_add_subgroup H t h)

end

namespace add_group_with_zero_nhd

local attribute [instance] add_group_with_zero_nhd.topological_space
local notation `Z` := add_group_with_zero_nhd.Z

variables {α : Type*}
variables {G : Type*} [add_group_with_zero_nhd G]

lemma nhds_eq_comap (g : G) : nhds g = comap (λ g', g' + -g) (Z G) :=
by rw [← nhds_zero_eq_Z, nhds_translation_add_neg g]
end add_group_with_zero_nhd

namespace topological_group
variables {G : Type*} {H : Type*}
variables [group G] [topological_space G] [topological_group G]
variables [group H] [topological_space H] [topological_group H]
variables (f : G → H) [is_group_hom f]


-- TODO when PR'ing to mathlib, make sure to include _right in the name
-- of this and nhds_translation_mul_inv
@[to_additive nhds_translation_add]
lemma nhds_translation_mul (g : G) :
  map (λ h, h*g) (nhds 1) = nhds g :=
begin
  rw ← nhds_translation_mul_inv g,
  apply map_eq_comap_of_inverse ; ext ; simp
end


@[to_additive nhds_translation_add_neg_left]
lemma nhds_translation_mul_inv_left (g : G) :
  comap (λ h, g⁻¹*h) (nhds 1) = nhds g :=
begin
  refine comap_eq_of_inverse (λ h, g*h) _ _ _,
  { funext x; simp },
  { suffices : tendsto (λ h,g⁻¹*h) (nhds g) (nhds (g⁻¹ * g)), { simpa },
    exact tendsto_mul tendsto_const_nhds tendsto_id },
  { suffices : tendsto (λ h, g*h) (nhds 1) (nhds (g*1)), { simpa },
    exact tendsto_mul tendsto_const_nhds tendsto_id }
end

@[to_additive nhds_translation_add_left]
lemma nhds_translation_mul_left (g : G) :
  map (λ h, g*h) (nhds 1) = nhds g :=
begin
  rw ← nhds_translation_mul_inv_left g,
  apply map_eq_comap_of_inverse ; ext ; simp
end

@[to_additive topological_add_group.continuous_of_continuous_at_zero]
lemma continuous_of_continuous_at_one (h : continuous_at f 1) :
  continuous f :=
begin
  replace h : map f (nhds 1) ≤ nhds 1, by rw ← is_group_hom.one f ; exact h,
  rw continuous_iff_continuous_at,
  intro g,
  have key : (f ∘ λ (h : G), g * h) = (λ (h : H), (f g) * h) ∘ f,
    by ext ; simp [is_group_hom.mul f],
  change map f (nhds g) ≤ nhds (f g),
  rw [← nhds_translation_mul_left g, ← nhds_translation_mul_left (f g),
      filter.map_comm key],
  exact map_mono h
end

@[to_additive topological_add_group.tendsto_nhds_iff]
lemma tendsto_nhds_iff {α : Type*} (f : α → H) (F : filter α) (h : H) :
  tendsto f F (nhds h) ↔ ∀ V ∈ nhds (1 : H), {a | f a * h⁻¹ ∈ V} ∈ F :=
let R := λ h', h' * h⁻¹,
    N := nhds (1 : H) in
calc tendsto f F (nhds h) ↔ map f F ≤ (nhds h) : iff.rfl
  ... ↔ map f F ≤ comap R N : by rw nhds_translation_mul_inv
  ... ↔ map R (map f F) ≤ N : map_le_iff_le_comap.symm
  ... ↔ map (λ a, f a * h⁻¹) F ≤ N : by rw filter.map_map

@[to_additive topological_add_group.tendsto_nhds_nhds_iff]
lemma tendsto_nhds_nhds_iff (f : G → H) (g : G) (h : H) :
  tendsto f (nhds g) (nhds h) ↔
  ∀ V ∈ nhds (1 : H), ∃ U ∈ nhds (1 : G), ∀ g', g'*g⁻¹ ∈ U → f g' * h⁻¹ ∈ V :=
by rw [tendsto_nhds_iff f, ← nhds_translation_mul_inv g] ; exact iff.rfl

end topological_group


section
variables (G : Type u) [add_comm_group G] [topological_space G] [topological_add_group G]

local attribute [instance] topological_add_group.to_uniform_space

-- Wedhorn Definition 5.31 page 38
definition is_complete_hausdorff : Prop := is_complete (univ : set G) ∧ is_hausdorff G
end


-- I used to think I would need the next section soon, but I no longer do.
-- I keep it because we'll want some form of this in mathlib at some point
section top_group_equiv
variables (G : Type*) [group G] [topological_space G] [topological_group G]
variables (H : Type*) [group H] [topological_space H] [topological_group H]

structure top_group_equiv extends homeomorph G H :=
(hom : is_group_hom to_fun)

infix ` ≃*ₜ `:50 := top_group_equiv

instance top_group_equiv.is_group_hom (h : G ≃*ₜ H) : is_group_hom h.to_homeomorph :=
h.hom
end top_group_equiv

namespace top_group_equiv
variables (G : Type*) [group G] [topological_space G] [topological_group G]
variables (H : Type*) [group H] [topological_space H] [topological_group H]
variables (K : Type*) [group K] [topological_space K] [topological_group K]

@[refl] def refl : G ≃*ₜ G :=
{ hom := is_group_hom.id,
  continuous_to_fun := continuous_id,
  continuous_inv_fun := continuous_id,
  ..equiv.refl _}

@[symm] def symm (h : G ≃*ₜ H) : H ≃*ₜ G :=
{ hom := ⟨λ n₁ n₂, function.injective_of_left_inverse h.left_inv begin
   rw h.hom.mul, unfold equiv.symm, rw [h.right_inv, h.right_inv, h.right_inv], end⟩,
  continuous_to_fun := h.continuous_inv_fun,
  continuous_inv_fun := h.continuous_to_fun,
  ..h.to_equiv.symm}

@[trans] def trans (h1 : G ≃*ₜ H) (h2 : H ≃*ₜ K) : (G ≃*ₜ K) :=
{ hom := is_group_hom.comp h1.to_homeomorph.to_equiv.to_fun h2.to_homeomorph.to_equiv.to_fun,
  continuous_to_fun := continuous.comp h1.continuous_to_fun h2.continuous_to_fun,
  continuous_inv_fun := continuous.comp h2.continuous_inv_fun h1.continuous_inv_fun,
  ..equiv.trans h1.to_equiv h2.to_equiv }

end top_group_equiv

-- Next secton will move to topology/basic.lean
section
variables {α : Type*} {β : Type*} [topological_space β]

/-- If a function is constant on some set of a proper filter then it converges along this filter -/
lemma exists_limit_of_ultimately_const {φ : α → β} {f : filter α} (hf : f ≠ ⊥)
{U : set α} (hU : U ∈ f) (h : ∀ x y ∈ U,  φ x = φ y) : ∃ b, tendsto φ f (nhds b) :=
begin
  have U_ne : U ≠ ∅,
  { intro U_empty,
    rw U_empty at hU,
    exact mt empty_in_sets_eq_bot.1 hf hU },
  cases exists_mem_of_ne_empty U_ne with x₀ x₀_in,
  use φ x₀,
  have : U ⊆ φ ⁻¹' {φ x₀},
  { intros x x_in,
    simp [h x x₀ x_in x₀_in] },
  have : tendsto φ f (pure $ φ x₀),
  { rw tendsto_pure,
    exact mem_sets_of_superset hU this},
  exact le_trans this (pure_le_nhds _)
end
end

-- The next section will be used to extend a valuation to the completion of a field (for the
-- valuation induced topology). The group Γ will be the value group, G = K^* and H = \hat{K}^*
-- (units of the completed field). φ will be the valuation restricted to K^*
section
open is_group_hom
variables {G : Type*} [group G] [topological_space G] [topological_group G]
variables {H : Type*} [group H] [topological_space H] [topological_group H]
variables {Γ : Type*} [group Γ] [topological_space Γ] [topological_group Γ] [regular_space Γ]

variables {ι : G → H} [is_group_hom ι] (de : dense_embedding ι)
variables {φ : G → Γ} [is_group_hom φ]

-- misc missing lemma, nothing to do with extensions of stuff

lemma mul_right_nhds_one {U : set G} (U_in : U ∈ nhds (1 : G)) (g : G) :
  (λ x, x*g) '' U ∈ nhds g :=
begin
  have l : function.left_inverse (λ (x : G), x * g⁻¹) (λ (x : G), x * g), from λ x, by simp,
  have r : function.right_inverse (λ (x : G), x * g⁻¹) (λ (x : G), x * g), from λ x, by simp,
  rw image_eq_preimage_of_inverse l r,
  have : continuous (λ (x : G), x * g⁻¹), from continuous_mul continuous_id continuous_const,
  apply this.tendsto g,
  simpa,
end


-- in Lean the "extension by continuity" of φ always exists, and extends φ.
example : ∀ g, (de.extend φ) (ι g) = φ g := de.extend_e_eq

-- But, without additional assumption, it gives junk outside the range of ι.
-- Here we explain how to make sure it's continuous, under the crucial assumption
-- is_open (ker φ) which will be true in our case because Γ is discrete

lemma continuous_extend_of_open_kernel (op_ker : is_open (ker φ)) : continuous (de.extend φ) :=
begin
  have : ∃ V, V ∈ nhds (1 : H) ∧ ker φ = ι ⁻¹' V,
  { have : ker φ ∈ nhds (1 : G),
      from mem_nhds_sets op_ker (is_submonoid.one_mem (ker φ)),
    rw [← de.induced, mem_comap_sets_of_inj de.inj] at this,
    rcases this with ⟨V, V_in, hV⟩,
    rw one ι at V_in,
    use [V, V_in, hV] },
  rcases this with ⟨V, V_in, hV⟩,
  have : ∃ V' ∈ nhds (1 : H), ∀ x y ∈ V', x*y⁻¹ ∈ V,
    from exists_nhds_split_inv V_in,
  rcases this with ⟨V', V'_in, hV'⟩,
  apply dense_embedding.continuous_extend,
  intro h,
  have : ι ⁻¹' ((λ x, x*h) '' V') ∈ comap ι (nhds h),
  { rw mem_comap_sets_of_inj de.inj,
    exact ⟨(λ (x : H), x * h) '' V', mul_right_nhds_one V'_in h, rfl⟩ },
  apply exists_limit_of_ultimately_const de.comap_nhds_neq_bot this, clear this,
  intros x y x_in y_in,
  rw mem_preimage_eq at x_in y_in,
  rcases x_in with ⟨vₓ, vₓ_in, hx⟩,
  rcases y_in with ⟨vy, vy_in, hy⟩,
  change vₓ * h = ι x at hx,
  change vy * h = ι y at hy,
  rw [inv_iff_ker φ, hV, mem_preimage_eq, mul ι, inv ι, ← hx, ← hy],
  simp [mul_assoc],
  simp [hV', *],
end
end
