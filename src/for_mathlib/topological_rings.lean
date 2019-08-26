import topology.algebra.ring
import topology.algebra.open_subgroup
import ring_theory.subring
import ring_theory.ideal_operations

import for_mathlib.topological_groups
import for_mathlib.topology

universes u v

local prefix 𝓝:100 := nhds
local infixr ` ×ᶠ `:51 := filter.prod

variables {A : Type u} {B : Type v}
variables [comm_ring A] [topological_space A] [topological_ring A]
variables [comm_ring B] [topological_space B] [topological_ring B]

open set topological_ring

instance subring_has_zero (R : Type u) [comm_ring R] (S : set R) [HS : is_subring S] : has_zero S :=
⟨⟨0, is_add_submonoid.zero_mem S⟩⟩

instance topological_subring (A₀ : set A) [is_subring A₀] : topological_ring A₀ :=
{ continuous_neg := continuous_subtype_mk _ $ (continuous_neg A).comp continuous_subtype_val,
  continuous_add := continuous_subtype_mk _ $ continuous_add
    (continuous_subtype_val.comp continuous_fst)
    ( continuous_subtype_val.comp continuous_snd),
  continuous_mul := continuous_subtype_mk _ $ continuous_mul
    (continuous_subtype_val.comp continuous_fst)
    (continuous_subtype_val.comp continuous_snd) }

lemma half_nhds {s : set A} (hs : s ∈ (nhds (0 : A))) :
  ∃ V ∈ (nhds (0 : A)), ∀ v w ∈ V, v * w ∈ s :=
begin
  have : ((λa:A×A, a.1 * a.2) ⁻¹' s) ∈ (nhds ((0, 0) : A × A)) :=
    tendsto_mul' (by simpa using hs),
  rw nhds_prod_eq at this,
  rcases filter.mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, filter.inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

-- lemma continuous_mul_left (a : A) : continuous (λ x, a * x) :=
-- continuous_mul continuous_const continuous_id
--
-- lemma continuous_mul_right (a : A) : continuous (λ x, x * a) :=
-- continuous_mul continuous_id continuous_const

lemma is_open_ideal_map_open_embedding {f : A → B} [is_ring_hom f]
  (emb : embedding f) (hf : is_open (range f)) (I : ideal A) (hI : is_open (↑I : set A)) :
  is_open (↑(I.map f) : set B) :=
open_add_subgroup.is_open_of_open_add_subgroup
  ⟨⟨f '' I, embedding_open emb hf hI, by apply_instance⟩, ideal.subset_span⟩

instance pi_topological_ring {I : Type*} {R : I → Type*} [∀ i, comm_ring (R i)] [∀ i, topological_space (R i)]
  [h : ∀ i, topological_ring (R i)] : topological_ring (Π (i : I), R i) :=
{ continuous_add := continuous_pi₂ (λ i, (h i).continuous_add),
  continuous_mul := continuous_pi₂ (λ i, (h i).continuous_mul),
  continuous_neg := continuous_pi₁ (λ i, (h i).continuous_neg) }

section
open function filter

lemma topological_ring.of_nice_nhds_zero (α : Type u) [ring α] [topological_space α]
  (hadd : tendsto (uncurry' ((+) : α → α → α)) (𝓝 0 ×ᶠ 𝓝 0) 𝓝 0)
  (hneg : tendsto (λ x, -x : α → α) 𝓝 0 𝓝 0)
  (hmul : tendsto (uncurry' ((*) : α → α → α)) (𝓝 0 ×ᶠ 𝓝 0) 𝓝 0)
  (hmul_left : ∀ (x₀ : α), tendsto (λ x : α, x₀ * x) 𝓝 0 𝓝 0)
  (hmul_right : ∀ (x₀ : α), tendsto (λ x : α, x * x₀) 𝓝 0 𝓝 0)
  (hleft : ∀ x₀ : α, 𝓝 x₀ = map (λ x, x₀+x) 𝓝 0) : topological_ring α :=
begin
  refine {..topological_add_group.of_nice_nhds_zero α hadd hneg hleft, ..},
  rw continuous_iff_continuous_at,
  rintro ⟨x₀, y₀⟩,
  rw [continuous_at, nhds_prod_eq, hleft x₀, hleft y₀, hleft (x₀*y₀), filter.prod_map_map_eq,
      tendsto_map'_iff],
  suffices :
    tendsto ((λ (x : α), x + x₀ * y₀) ∘ (λ (p : α × α), p.1 + p.2) ∘
              (λ (p : α × α), (p.1*y₀ + x₀*p.2, p.1*p.2)))
            (𝓝 0 ×ᶠ 𝓝 0) (map (λ (x : α), x + x₀ * y₀) 𝓝 0),
  { convert this using 1,
    { ext, simp only [comp_app, mul_add, add_mul], abel },
    { simp only [add_comm] } },
  refine tendsto_map.comp (hadd.comp (tendsto.prod_mk _ hmul)),
  { change tendsto ((λ p : α × α, p.1 + p.2) ∘ λ (x : α × α), (x.1 * y₀, x₀ * x.2)) (𝓝 0 ×ᶠ 𝓝 0) 𝓝 0,
    exact hadd.comp (tendsto.prod_mk ((hmul_right y₀).comp tendsto_fst)
                                     ((hmul_left  x₀).comp tendsto_snd)) }
end

end
local attribute [instance] pointwise_mul pointwise_add

class ring_filter_basis (α : Type u) [ring α] extends add_group_filter_basis α :=
(mul : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U)
(mul_left : ∀ (x₀ : α) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x₀*x) ⁻¹' U)
(mul_right : ∀ (x₀ : α) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x*x₀) ⁻¹' U)


namespace ring_filter_basis
lemma is_top_ring {α : Type u} [ring α] [t : topological_space α] (b : ring_filter_basis α)
  (hnhds : ∀ x₀ : α, 𝓝 x₀ = b.to_add_group_filter_basis.N x₀) : topological_ring α :=
begin
  let basis := b.to_filter_basis,
  have hnhds0 : 𝓝 0 = basis.filter, by rw [hnhds, b.to_add_group_filter_basis.N_zero],
  apply topological_ring.of_nice_nhds_zero,
  { rw [hnhds0, ← basis.prod_filter, filter_basis.tendsto_both],
    intros V V_in,
    rcases add_group_filter_basis.add V_in with ⟨W, W_in, hW⟩,
    use [set.prod W W, filter_basis.mem_prod_of_mem W_in W_in],
    rwa [pointwise_add_eq_image, image_subset_iff] at hW },
  { rw [hnhds0, basis.tendsto_both],
    exact b.neg },
  { rw [hnhds0, ← basis.prod_filter, filter_basis.tendsto_both],
    intros V V_in,
    rcases ring_filter_basis.mul V_in with ⟨W, W_in, hW⟩,
    use [set.prod W W, filter_basis.mem_prod_of_mem W_in W_in],
    rwa [pointwise_mul_eq_image, image_subset_iff] at hW },
  { simp only [hnhds0, basis.tendsto_both],
    exact b.mul_left },
  { simp only [hnhds0, basis.tendsto_both],
    exact b.mul_right },
  { exact hnhds0.symm ▸ hnhds }
end

lemma is_topological_ring (α : Type u) [ring α] [t : topological_space α] [b : ring_filter_basis α]
  (h : t = b.to_add_group_filter_basis.topology) : topological_ring α :=
begin
  let nice := b.to_add_group_filter_basis.N_is_nice,
  apply b.is_top_ring,
  rw h,
  intro x₀,
  exact topological_space.nhds_mk_of_nhds _ _ nice.1 nice.2,
end

local attribute [instance] add_group_filter_basis.topology

--meta instance cut_trace : has_bind tactic := by apply_instance

def workaround (α : Type u) [ring α] [ring_filter_basis α] : topological_space α :=
begin
  apply add_group_filter_basis.topology,
  apply_instance,
end
local attribute [instance] workaround

lemma topological_ring (α : Type u) [ring α] [b : ring_filter_basis α] : topological_ring α :=
is_topological_ring α rfl
end ring_filter_basis
