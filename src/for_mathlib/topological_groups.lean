import tactic.abel

import topology.algebra.group
import topology.algebra.uniform_ring
import ring_theory.subring

import for_mathlib.topology
import for_mathlib.filter
import for_mathlib.data.set.basic
import algebra.pointwise

/-
open filter function

universe u

class filter_at_one (α : Type u) [group α] :=
(F : filter α)
(one_in : pure 1 ≤ F) -- we could ask instead that Z ≠ ⊥
(mul {} : tendsto (uncurry' ((*) : α → α → α)) (F.prod F) F)
(inv {} : tendsto (λ x: α, x⁻¹) F F)
(conj {} : ∀ x₀ : α, tendsto (λ x: α, x₀*x*x₀⁻¹) F F).

namespace filter_at_one

def topology (α : Type u) [group α] [filter_at_one α] : topological_space α :=
topological_space.mk_of_nhds $ λa, map (λx, a*x) (F α)

local attribute [instance] topology
lemma topological_group (α : Type u) [group α] [filter_at_one α]: topological_group α :=
sorry

end filter_at_one

Using the above setup, we get :

filter_at_one.topological_group :
  ∀ (α : Type u_1) [_inst_1 : group α] [_inst_2 : @filter_at_one α _inst_1],
    @topological_group α (@filter_at_one.topology α _inst_1 _inst_2) _inst_1

So this lemma (which could be then turned into a local instance) is only about the
topology built by `filter_at_one.topology`. It doesn't not say anything about
a group endowed by a random topology that happens to satisfies the axioms of filter_at_one.
-/
universe u
open filter function set topological_space
local infixr ` ×ᶠ `:51 := filter.prod
local prefix 𝓝:100 := nhds

@[to_additive topological_add_monoid.of_comm_of_nice_nhds_zero]
lemma topological_monoid.of_comm_of_nice_nhds_one (α : Type u) [comm_monoid α] [topological_space α]
  (hmul : tendsto (uncurry' ((*) : α → α → α)) (𝓝 1 ×ᶠ 𝓝 1) 𝓝 1)
  (hleft : ∀ x₀ : α, 𝓝 x₀ = map (λ x, x₀*x) 𝓝 1) : topological_monoid α :=
{ continuous_mul := begin
    rw continuous_iff_continuous_at,
    rintros ⟨x₀, y₀⟩,
    have key : (λ (p : α × α), x₀ * p.1 * (y₀ * p.2)) =
      ((λ x, x₀*y₀*x) ∘ (uncurry' (*))),
    { ext,
      change x₀ * x.1 * (y₀ * x.2) = x₀ * y₀ * (x.1 *  x.2),
      ac_refl },

    calc map (λ (p : α × α), p.1 * p.2) 𝓝 (x₀, y₀)
        = map (λ (p : α × α), p.1 * p.2) (𝓝 x₀ ×ᶠ 𝓝 y₀)
            : by rw nhds_prod_eq
    ... = map (λ (p : α × α), x₀ * p.1 * (y₀ * p.2)) ((𝓝 1) ×ᶠ (𝓝 1))
            : by rw [hleft x₀, hleft y₀, prod_map_map_eq, filter.map_map]
    ... = map ((λ x, x₀*y₀*x) ∘ (uncurry' (*))) ((𝓝 1) ×ᶠ (𝓝 1)) : by rw key
    ... = map (λ x, x₀*y₀*x) (map (uncurry' (*)) ((𝓝 1) ×ᶠ (𝓝 1)))   : by rw filter.map_map
    ... ≤ map (λ x, x₀*y₀*x) (𝓝 1)   : map_mono hmul
    ... = 𝓝 (x₀*y₀)   : (hleft _).symm
  end }

protected meta def prove_conj : tactic unit :=
`[ intro x₀,
   convert continuous_id.continuous_at,
   simpa [mul_comm, inv_mul_cancel_left]]

@[to_additive topological_add_group.of_nice_nhds_zero]
lemma topological_group.of_nice_nhds_one (α : Type u) [group α] [topological_space α]
  (hmul : tendsto (uncurry' ((*) : α → α → α)) ((𝓝 1).prod 𝓝 1) 𝓝 1)
  (hinv : tendsto (λ x : α, x⁻¹) 𝓝 1 𝓝 1)
  (hleft : ∀ x₀ : α, 𝓝 x₀ = map (λ x, x₀*x) 𝓝 1)
  (hconj : ∀ x₀ : α, tendsto (λ x: α, x₀*x*x₀⁻¹) 𝓝 1 𝓝 1 . prove_conj) : topological_group α :=
{ continuous_mul := begin
    rw continuous_iff_continuous_at,
    rintros ⟨x₀, y₀⟩,
    have key : (λ (p : α × α), x₀ * p.1 * (y₀ * p.2)) =
      ((λ x, x₀*y₀*x) ∘ (uncurry' (*)) ∘ ((λ x, y₀⁻¹*x*y₀) ⨯ id)),
      by { ext, simp [uncurry', prod.map', mul_assoc] },
    specialize hconj y₀⁻¹, rw inv_inv at hconj,
    calc map (λ (p : α × α), p.1 * p.2) 𝓝 (x₀, y₀)
        = map (λ (p : α × α), p.1 * p.2) (𝓝 x₀ ×ᶠ 𝓝 y₀)
            : by rw nhds_prod_eq
    ... = map (λ (p : α × α), x₀ * p.1 * (y₀ * p.2)) ((𝓝 1) ×ᶠ (𝓝 1))
            : by rw [hleft x₀, hleft y₀, prod_map_map_eq, filter.map_map]
    ... = map (((λ x, x₀*y₀*x) ∘ (uncurry' (*))) ∘ ((λ x, y₀⁻¹*x*y₀) ⨯ id))((𝓝 1) ×ᶠ (𝓝 1))
            : by rw key
    ... = map ((λ x, x₀*y₀*x) ∘ (uncurry' (*))) ((map  (λ x, y₀⁻¹*x*y₀) 𝓝 1) ×ᶠ (𝓝 1))
            : by rw [← filter.map_map, filter.map_prod_prod, map_id]
    ... ≤ map ((λ x, x₀*y₀*x) ∘ (uncurry' (*))) ((𝓝 1) ×ᶠ (𝓝 1))
            : map_mono (filter.prod_mono hconj $ le_refl _)
    ... = map (λ x, x₀*y₀*x) (map (uncurry' (*)) ((𝓝 1) ×ᶠ (𝓝 1)))   : by rw filter.map_map
    ... ≤ map (λ x, x₀*y₀*x) (𝓝 1)   : map_mono hmul
    ... = 𝓝 (x₀*y₀)   : (hleft _).symm
  end,
  continuous_inv := begin
    rw continuous_iff_continuous_at,
    rintros x₀,
    have key : (λ x, (x₀*x)⁻¹) = (λ x, x₀⁻¹*x) ∘ (λ x, x₀*x*x₀⁻¹) ∘ (λ x, x⁻¹),
      by {ext ; simp[mul_assoc] },
    calc map (λ x, x⁻¹) (𝓝 x₀)
        = map (λ x, x⁻¹) (map (λ x, x₀*x) 𝓝 1) : by rw hleft
    ... = map (λ x, (x₀*x)⁻¹) 𝓝 1 : by rw filter.map_map
    ... = map (((λ x, x₀⁻¹*x) ∘ (λ x, x₀*x*x₀⁻¹)) ∘ (λ x, x⁻¹)) 𝓝 1 : by rw key
    ... = map ((λ x, x₀⁻¹*x) ∘ (λ x, x₀*x*x₀⁻¹)) _ : by rw ← filter.map_map
    ... ≤ map ((λ x, x₀⁻¹ * x) ∘ λ x, x₀ * x * x₀⁻¹) (𝓝 1) : map_mono hinv
    ... = map (λ x, x₀⁻¹ * x) (map (λ x, x₀ * x * x₀⁻¹) (𝓝 1)) : filter.map_map
    ... ≤ map (λ x, x₀⁻¹ * x) 𝓝 1 : map_mono (hconj x₀)
    ... = 𝓝 x₀⁻¹ : (hleft _).symm
  end }


@[to_additive topological_add_group.of_comm_of_nice_nhds_zero]
lemma topological_group.of_comm_of_nice_nhds_one (α : Type u) [comm_group α] [topological_space α]
  (hmul : tendsto (uncurry' ((*) : α → α → α)) ((𝓝 1).prod 𝓝 1) 𝓝 1)
  (hinv : tendsto (λ x : α, x⁻¹) 𝓝 1 𝓝 1)
  (hleft : ∀ x₀ : α, 𝓝 x₀ = map (λ x, x₀*x) 𝓝 1) : topological_group α :=
topological_group.of_nice_nhds_one α hmul hinv hleft

open set
local attribute [instance] pointwise_mul pointwise_add

class group_filter_basis (α : Type u) [group α] extends filter_basis α :=
(one : ∀ {U}, U ∈ sets → (1 : α) ∈ U)
(mul : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U)
(inv : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x⁻¹) ⁻¹' U)
(conj : ∀ x₀, ∀ U ∈ sets, ∃ V ∈ sets, V ⊆ (λ x, x₀*x*x₀⁻¹) ⁻¹' U)

class add_group_filter_basis (α : Type u) [add_group α] extends filter_basis α :=
(zero : ∀ {U}, U ∈ sets → (0 : α) ∈ U)
(add : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V + V ⊆ U)
(neg : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, -x) ⁻¹' U)
(conj : ∀ x₀, ∀ U ∈ sets, ∃ V ∈ sets, V ⊆ (λ x, x₀+x-x₀) ⁻¹' U)

attribute [to_additive add_group_filter_basis] group_filter_basis
attribute [to_additive add_group_filter_basis.zero] group_filter_basis.one
attribute [to_additive add_group_filter_basis.add] group_filter_basis.mul
attribute [to_additive add_group_filter_basis.neg] group_filter_basis.inv
attribute [to_additive add_group_filter_basis.conj] group_filter_basis.conj
attribute [to_additive add_group_filter_basis.to_filter_basis] group_filter_basis.to_filter_basis


/- -- We didn't use class directly because we still want α to be an explicit argument of projections
attribute [class] group_filter_basis
attribute [class] add_group_filter_basis
 -/
instance group_filter_basis.has_mem {α : Type*} [group α] : has_mem (set α) (group_filter_basis α) := ⟨λ s f, s ∈ f.sets⟩
instance add_group_filter_basis.has_mem {α : Type*} [add_group α] : has_mem (set α) (add_group_filter_basis α) := ⟨λ s f, s ∈ f.sets⟩

attribute [to_additive add_group_filter_basis.has_mem] group_filter_basis.has_mem

namespace group_filter_basis
variables {α : Type*} [group α]

@[to_additive add_group_filter_basis.add_subset_self]
lemma prod_subset_self (f : group_filter_basis α) {U : set α} (h : U ∈ f) : U ⊆ U*U :=
λ x x_in, (mul_one x) ▸ mul_mem_pointwise_mul x_in $ group_filter_basis.one h

/-- The neighborhood function of a `group_filter_basis` -/
@[to_additive add_group_filter_basis.N]
def N (f : group_filter_basis α) : α → filter α :=
λ x, map (λ y, x*y) f.to_filter_basis.filter

attribute [to_additive add_group_filter_basis.N.equations._eqn_1]
  group_filter_basis.N.equations._eqn_1

@[simp, to_additive add_group_filter_basis.N_zero]
lemma N_one (f : group_filter_basis α) : f.N 1 = f.to_filter_basis.filter :=
by simpa [N, map_id]

@[to_additive add_group_filter_basis.mem_N]
lemma mem_N (f : group_filter_basis α) (x : α) (U : set α) :
  U ∈ f.N x ↔ ∃ V ∈ f, (λ y, x*y) '' V ⊆ U :=
by simpa [N, mem_map, filter_basis.mem_filter, image_subset_iff]

@[to_additive add_group_filter_basis.mem_N_of_mem]
lemma mem_N_of_mem (f : group_filter_basis α) (x : α) {U : set α} (h : U ∈ f) :
(λ y, x*y) '' U ∈ f.N x :=
by { rw mem_N, use [U, h] }

@[to_additive add_group_filter_basis.N_is_nice]
lemma N_is_nice (f : group_filter_basis α) :
  (pure ≤ f.N) ∧
  ∀ {a s}, s ∈ f.N a → ∃ t ∈ f.N a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ f.N a' :=
begin
  split,
  { intros x U U_in,
    rw f.mem_N at U_in,
    rcases U_in with ⟨V, V_in, H⟩,
    simpa [mem_pure] using H (mem_image_of_mem _ (group_filter_basis.one V_in)) },
  { intros x U U_in,
    rw f.mem_N at U_in,
    rcases U_in with ⟨V, V_in, H⟩,
    rcases group_filter_basis.mul V_in with ⟨W, W_in, hW⟩,
    use [(λ y, x*y) '' W, image_mem_map (filter_basis.mem_filter_of_mem W_in)],
    split,
    { rw image_subset_iff at H ⊢,
      exact subset.trans (subset.trans (f.prod_subset_self W_in) hW) H},
    { rintros y ⟨t, tW, rfl⟩,
      rw f.mem_N,
      use [W, W_in],
      apply subset.trans _ H, clear H,
      rintros z ⟨w, wW, rfl⟩,
      exact ⟨t*w, hW (mul_mem_pointwise_mul tW wW), by simp [mul_assoc]⟩ } },
end

@[to_additive add_group_filter_basis.is_top_group]
lemma is_top_group {α : Type u} [group α] (basis : group_filter_basis α) [topological_space α]
  (hnhds : ∀ x₀ : α, 𝓝 x₀ = basis.N x₀) : topological_group α :=
begin
  have hnhds1 : 𝓝 1 = basis.to_filter_basis.filter, by rw [hnhds 1, N_one],
  apply topological_group.of_nice_nhds_one,
  { rw [hnhds1, ← basis.to_filter_basis.prod_filter, filter_basis.tendsto_both],
    intros V V_in,
    rcases group_filter_basis.mul V_in with ⟨W, W_in, hW⟩,
    use [set.prod W W, filter_basis.mem_prod_of_mem W_in W_in],
    rwa [pointwise_mul_eq_image, image_subset_iff] at hW },
  { rw [hnhds1, basis.to_filter_basis.tendsto_both],
    exact basis.inv },
  { exact hnhds1.symm ▸ hnhds },
  { intro x₀,
    rw [hnhds1, basis.to_filter_basis.tendsto_both],
    exact  group_filter_basis.conj x₀ }
end

/-- The topological space structure coming a group filter basis. -/
@[to_additive add_group_filter_basis.topology]
def topology {α : Type u} [group α] (basis : group_filter_basis α) : topological_space α :=
topological_space.mk_of_nhds basis.N

/-- The topological space structure coming a group filter basis. Version using tc resolution -/
@[to_additive add_group_filter_basis.to_topological_space]
def to_topological_space {α : Type u} [group α] [basis : group_filter_basis α] : topological_space α :=
basis.topology

@[to_additive add_group_filter_basis.nhds_eq]
lemma nhds_eq {α : Type u} [group α] (basis : group_filter_basis α)
  [t : topological_space α] (h : t = basis.topology) {x₀ : α} :
  𝓝 x₀ = basis.N x₀ :=
by rw [h, nhds_mk_of_nhds _ x₀ basis.N_is_nice.1 basis.N_is_nice.2]

@[to_additive add_group_filter_basis.nhds_zero_eq]
lemma nhds_one_eq {α : Type u} [group α] (basis : group_filter_basis α)
  [t : topological_space α] (h : t = basis.topology) :
  𝓝 (1 : α) = basis.to_filter_basis.filter :=
by { rw basis.nhds_eq h, simp only [N, one_mul], exact map_id }

@[to_additive add_group_filter_basis.mem_nhds]
lemma mem_nhds {α : Type u} [group α] (basis : group_filter_basis α)
  [t : topological_space α] (h : t = basis.topology) {x₀ : α} {U : set α} :
  U ∈ 𝓝 x₀ ↔ ∃ V ∈ basis, V ⊆ (λ x, x₀ * x) ⁻¹' U :=
begin
  rw basis.nhds_eq h,
  exact filter_basis.mem_filter basis.to_filter_basis
end

@[to_additive add_group_filter_basis.is_topological_group]
lemma is_topological_group {α : Type u} [group α] (basis : group_filter_basis α)
  [t : topological_space α] (h : t = basis.topology) : topological_group α :=
begin
  apply basis.is_top_group,
  rw h,
  exact λ x, nhds_mk_of_nhds _ x basis.N_is_nice.1 basis.N_is_nice.2
end


/-- The neighborhood basis on a group coming from a group filter basis -/
def nhds_basis {α : Type u} [group α] (basis : group_filter_basis α)
  [t : topological_space α] (h : t = basis.topology) : nhds_basis α :=
{ B := λ x₀, filter_basis.map (λ x, x₀*x) basis.to_filter_basis,
  is_nhds := λ x₀, by rw [← filter_basis.map_filter, h,
                          nhds_mk_of_nhds _ x₀ basis.N_is_nice.1 basis.N_is_nice.2, N] }


local attribute [instance] group_filter_basis.to_topological_space

-- The following can be made an instance when needed
def to_nhds_basis {α : Type u} [group α] [basis : group_filter_basis α]
   : _root_.nhds_basis α := basis.nhds_basis rfl

attribute [to_additive add_group_filter_basis.nhds_basis._proof_1] nhds_basis._proof_1
attribute [to_additive add_group_filter_basis.nhds_basis] nhds_basis
attribute [to_additive add_group_filter_basis.to_nhds_basis._proof_1] to_nhds_basis._proof_1
attribute [to_additive add_group_filter_basis.to_nhds_basis] to_nhds_basis

local attribute [instance] group_filter_basis.to_nhds_basis add_group_filter_basis.to_nhds_basis

@[to_additive add_group_filter_basis.mem_nhds_basis]
lemma mem_nhds_basis {α : Type u} [group α] [basis : group_filter_basis α] {s : set α} {x₀ : α} :
s ∈ nhds_basis.B x₀ ↔ (λ x, x₀*x) ⁻¹' s ∈ basis.to_filter_basis.sets :=
begin
  change s ∈ filter_basis.map (λ x, x₀*x) basis.to_filter_basis ↔ _,
  rw filter_basis.mem_map,
  split ; intro h,
  { rcases h with ⟨U, h, rfl⟩,
    rw preimage_image_eq,
    exact h,
    intros x y, simp },
  { use [(λ (x : α), x₀ * x) ⁻¹' s, h],
    rw image_preimage_eq,
    intros y,
    use [x₀⁻¹*y], simp }
end
end group_filter_basis



section
variables {G : Type u} [add_comm_group G]

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
  replace h : map f (nhds 1) ≤ nhds 1, by rw ← is_group_hom.map_one f ; exact h,
  rw continuous_iff_continuous_at,
  intro g,
  have key : (f ∘ λ (h : G), g * h) = (λ (h : H), (f g) * h) ∘ f,
    by ext ; simp [is_group_hom.map_mul f],
  change map f (nhds g) ≤ nhds (f g),
  rw [← nhds_translation_mul_left g, ← nhds_translation_mul_left (f g),
      filter.map_comm key],
  exact map_mono h
end

@[to_additive topological_add_group.tendsto_nhds_iff']
lemma tendsto_nhds_iff {α : Type*} (f : α → H) (F : filter α) (h : H) :
  tendsto f F (nhds h) ↔ ∀ V ∈ nhds (1 : H), {a | f a * h⁻¹ ∈ V} ∈ F :=
let R := λ h', h' * h⁻¹,
    N := nhds (1 : H) in
calc tendsto f F (nhds h) ↔ map f F ≤ (nhds h) : iff.rfl
  ... ↔ map f F ≤ comap R N : by rw nhds_translation_mul_inv
  ... ↔ map R (map f F) ≤ N : map_le_iff_le_comap.symm
  ... ↔ map (λ a, f a * h⁻¹) F ≤ N : by rw filter.map_map

@[to_additive topological_add_group.tendsto_nhds_nhds_iff']
lemma tendsto_nhds_nhds_iff (f : G → H) (g : G) (h : H) :
  tendsto f (nhds g) (nhds h) ↔
  ∀ V ∈ nhds (1 : H), ∃ U ∈ nhds (1 : G), ∀ g', g'*g⁻¹ ∈ U → f g' * h⁻¹ ∈ V :=
by rw [tendsto_nhds_iff f, ← nhds_translation_mul_inv g] ; exact iff.rfl
end topological_group

namespace topological_add_group
-- `to_additive` generates statements using `g + -h` instead of `g-h`, let's fix that

variables {G : Type*} [add_group G] [topological_space G] [topological_add_group G]
variables {H : Type*} [add_group H] [topological_space H] [topological_add_group H]

lemma tendsto_nhds_iff {α : Type*} (f : α → H) (F : filter α) (h : H) :
    tendsto f F (nhds h) ↔ ∀ (V : set H), V ∈ nhds (0 : H) → {a : α | f a - h ∈ V} ∈ F :=
topological_add_group.tendsto_nhds_iff' _ _ _

lemma tendsto_nhds_nhds_iff (f : G → H) (g : G) (h : H) :
  tendsto f (nhds g) (nhds h) ↔
  ∀ V ∈ nhds (0 : H), ∃ U ∈ nhds (0 : G), ∀ g', g' - g ∈ U → f g' - h ∈ V :=
topological_add_group.tendsto_nhds_nhds_iff' _ _ _
end topological_add_group

namespace add_group_with_zero_nhd
variables {α : Type*} [add_group_with_zero_nhd α]
open filter

lemma nhds_eq' (a : α) : nhds a = map (λx, a + x) (Z α) :=
by convert nhds_eq a ; ext ; simp

end add_group_with_zero_nhd



section
variables (G : Type u) [add_comm_group G] [topological_space G] [topological_add_group G]

local attribute [instance] topological_add_group.to_uniform_space
local attribute [instance] topological_add_group_is_uniform

lemma topological_add_group.separated_iff_zero_closed : separated G ↔ is_closed ({0} : set G) :=
begin
  unfold separated,
  rw ← closure_eq_iff_is_closed,
  split ; intro h,
  { apply subset.antisymm,
    { intros x x_in,
      have := group_separation_rel x 0,
      rw sub_zero at this,
      rw [← this, h] at x_in,
      change x = 0 at x_in,
      simp [x_in] },
    { exact subset_closure  } },
  { ext p,
    cases p with x y,
    rw [group_separation_rel x, h, mem_singleton_iff, sub_eq_zero_iff_eq],
    refl }
end

lemma topological_add_group.separated_of_zero_sep
  (H : ∀ x : G, x ≠ 0 → ∃ U ∈ nhds (0 : G), x ∉ U) : separated G:=
begin
  rw topological_add_group.separated_iff_zero_closed,
  rw [← is_open_compl_iff, is_open_iff_mem_nhds],
  intros x x_not,
  have : x ≠ 0, from mem_compl_singleton_iff.mp x_not,
  rcases H x this with ⟨U, U_in, xU⟩,
  rw ← nhds_zero_symm G at U_in,
  rcases U_in with ⟨W, W_in, UW⟩,
  rw ← nhds_translation_add_neg_left x,
  use [W, W_in],
  rw subset_compl_comm,
  suffices : -x ∉ W, by simp[this],
  intro h,
  exact xU (UW h)
end

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
   rw h.hom.map_mul, unfold equiv.symm, rw [h.right_inv, h.right_inv, h.right_inv], end⟩,
  continuous_to_fun := h.continuous_inv_fun,
  continuous_inv_fun := h.continuous_to_fun,
  ..h.to_equiv.symm}

@[trans] def trans (h1 : G ≃*ₜ H) (h2 : H ≃*ₜ K) : (G ≃*ₜ K) :=
{ hom := is_group_hom.comp h1.to_homeomorph.to_equiv.to_fun h2.to_homeomorph.to_equiv.to_fun,
  continuous_to_fun := h2.continuous_to_fun.comp h1.continuous_to_fun,
  continuous_inv_fun := h1.continuous_inv_fun.comp h2.continuous_inv_fun,
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

variables {ι : G → H} [is_group_hom ι] (dι : dense_inducing ι)
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


lemma continuous_extend_of_open_kernel (op_ker : is_open (ker φ)) : continuous (dι.extend φ) :=
begin
  have : ∃ V, V ∈ nhds (1 : H) ∧ ι ⁻¹' V ⊆ ker φ,
  { have : ker φ ∈ nhds (1 : G),
      from mem_nhds_sets op_ker (is_submonoid.one_mem (ker φ)),
    rw [dι.nhds_eq_comap, mem_comap_sets] at this,
    rcases this with ⟨V, V_in, hV⟩,
    rw map_one ι at V_in,
    use [V, V_in, hV] },
  rcases this with ⟨V, V_in, hV⟩,
  have : ∃ V' ∈ nhds (1 : H), ∀ x y ∈ V', x*y⁻¹ ∈ V,
    from exists_nhds_split_inv V_in,
  rcases this with ⟨V', V'_in, hV'⟩,
  refine dι.continuous_extend _,
  intro h,
  have : ι ⁻¹' ((λ x, x*h) '' V') ∈ comap ι (nhds h),
    from ⟨(λ (x : H), x * h) '' V', mul_right_nhds_one V'_in h, subset.refl _⟩,
  apply exists_limit_of_ultimately_const dι.comap_nhds_neq_bot this, clear this,
  intros x y x_in y_in,
  rw mem_preimage at x_in y_in,
  rcases x_in with ⟨vₓ, vₓ_in, hx⟩,
  rcases y_in with ⟨vy, vy_in, hy⟩,
  change vₓ * h = ι x at hx,
  change vy * h = ι y at hy,
  rw inv_iff_ker φ,
  apply hV,
  rw [mem_preimage, map_mul ι, map_inv ι, ← hx, ← hy, mul_assoc, mul_inv_rev, mul_inv_cancel_left],
  simp only [hV', *],
end
end

instance discrete_top_group {G : Type*} [group G] [topological_space G] [discrete_topology G] :
  topological_group G :=
{ continuous_mul := continuous_of_discrete_topology,
  continuous_inv := continuous_of_discrete_topology }

/- section top_group_extend
open is_group_hom
variables {G : Type*} [group G] [topological_space G] [topological_group G]
variables {H : Type*} [group H] [topological_space H] [topological_group H]
variables {L : Type*} [group L] [topological_space L] [topological_group L]
[t2_space L]

variables {ι : G → H} [is_group_hom ι] (de : dense_inducing ι)
variables {φ : G → L} [is_group_hom φ]

lemma topological_group.extend_is_group_hom (hφ : continuous φ) (h : continuous (de.extend φ)) :
  is_group_hom (de.extend φ) :=
sorry
-- TODO: Fix is_closed_property2 in mathlib. It has nothing to do with dense embedding. Need
-- dense_range.prod etc.
/- ⟨begin
  let Φ := de.extend φ,
  let P := λ x y : H, Φ (x*y) = Φ x*Φ y,
  have closed : is_closed { q : H × H | P q.1 q.2 } :=
    have c1 : continuous (λ q : H × H, Φ (q.1 * q.2)), from h.comp continuous_mul',
    have c2 : continuous (λ q : H × H, Φ q.1 * Φ q.2),
      from continuous_mul (h.comp continuous_fst) (h.comp continuous_snd),
  is_closed_eq c1 c2,

  apply is_closed_property2 de closed,
  intros x y,
  dsimp [P, Φ],
  rw ← is_group_hom.map_mul ι,
  repeat { rw dense_embedding.extend_e_eq },
  rw is_group_hom.map_mul φ
end⟩ -/
end top_group_extend
 -/
