import for_mathlib.nonarchimedean.basic
import for_mathlib.topological_rings

open set filter function lattice add_group_with_zero_nhd

--local attribute [instance] pointwise_mul pointwise_add
local attribute [instance] set.pointwise_mul_semiring
local attribute [instance] set.pointwise_mul_action

local notation `𝓝` x: 70 := nhds x

class subgroups_basis (A : Type*) [ring A] extends filter_basis A :=
[sub_groups {} : ∀ {G}, G ∈ sets → is_add_subgroup G]
(h_mul : ∀ {G}, G ∈ sets → ∃ H, H ∈ sets ∧ H * H ⊆ G)
(h_left_mul : ∀ x : A, ∀ {G}, G ∈ sets → ∃ H, H ∈ sets ∧ H ⊆ (λ y : A, x*y) ⁻¹' G)
(h_right_mul : ∀ x : A, ∀ {G}, G ∈ sets → ∃ H, H ∈ sets ∧ H ⊆ (λ y : A, y*x) ⁻¹' G)

namespace subgroups_basis
variables (A : Type*) [ring A] [subgroups_basis A]

instance to_ring_filter_basis : ring_filter_basis A :=
{ zero := begin
    intros G G_in,
    haveI := subgroups_basis.sub_groups G_in,
    exact is_add_submonoid.zero_mem G,
  end,
  add := begin
    intros G G_in,
    use [G, G_in],
    haveI := subgroups_basis.sub_groups G_in,
    rintro _ ⟨x, x_in, y, y_in, rfl⟩,
    exact is_add_submonoid.add_mem x_in y_in,
  end,
  neg := begin
    intros G G_in,
    use [G, G_in],
    intros x x_in,
    haveI : is_add_subgroup G := subgroups_basis.sub_groups G_in,
    apply is_add_subgroup.neg_mem x_in
  end,
  conj := begin
    intros x₀ U U_in,
    use [U, U_in],
    intros x x_in,
    simp [x_in]
  end,
  mul := λ G G_in, by simpa using h_mul G_in,
  mul_left :=  λ x₀ G G_in, by simpa using h_left_mul x₀ G_in,
  mul_right := λ x₀ G G_in, by simpa using h_right_mul x₀ G_in,
  ..‹subgroups_basis A› }

open subgroups_basis

def basis : set (set A) := (subgroups_basis.to_filter_basis A).sets

def topology : topological_space A :=
  (subgroups_basis.to_ring_filter_basis A).to_add_group_filter_basis.topology

lemma is_op [t : topological_space A] (h : t = topology A) {G : set A} (hG : G ∈ basis A) :
  is_open G :=
begin
  haveI := subgroups_basis.sub_groups hG,
  rw is_open_iff_mem_nhds,
  intros a ha,
  exact (add_group_filter_basis.mem_nhds
          (subgroups_basis.to_ring_filter_basis A).to_add_group_filter_basis h).2
        ⟨G, hG, λ g hg, is_add_submonoid.add_mem ha hg⟩
end

local attribute [instance] subgroups_basis.topology

def nhds_basis : nhds_basis A :=
(subgroups_basis.to_ring_filter_basis A).to_add_group_filter_basis.nhds_basis rfl

local attribute [instance] subgroups_basis.nhds_basis

variables {A}

lemma mem_nhds {s : set A} {x : A} : s ∈ 𝓝 x ↔ ∃ G ∈ basis A, {y | y - x ∈ G} ⊆ s :=
begin
  rw add_group_filter_basis.mem_nhds _ rfl,
  apply exists_congr,
  intro t,
  apply exists_congr,
  intro h,
  rw ← image_subset_iff,
  have l :left_inverse (λ y, y - x) (λ y, x + y),
  { intro y, simp only [], abel, },
  have r :right_inverse (λ y, y - x) (λ y, x + y),
  { intro y, simp only [], abel, },
  rw image_eq_preimage_of_inverse l r,
  exact iff.rfl
end

lemma mem_nhds_zero {s : set A} : s ∈ 𝓝 (0 : A) ↔ ∃ G ∈ basis A, G ⊆ s :=
by simp [mem_nhds]

lemma tendsto_into {α : Type*} (F : filter α) (f : α → A) (a : A) :
  tendsto f F 𝓝 a ↔ ∀ G ∈ basis A, {x | f x - a ∈ G} ∈ F :=
begin
  rw nhds_basis.tendsto_into,
  split ; intros h,
  { intros G G_in,
    specialize h {y : A | y - a ∈ G},
    rw add_group_filter_basis.mem_nhds_basis at h,
    apply h,
    simpa using G_in },
  { intros U U_in,
    rw add_group_filter_basis.mem_nhds_basis at U_in,
    specialize h _ U_in,
    change {x : α | a + (f x - a) ∈ U} ∈ F at h,
    simpa only [show ∀ x, a + (f x - a) = f x, by intros ; abel] using h },
end

lemma continuous_into {α : Type*} [topological_space α] (f : α → A) :
  continuous f ↔ ∀ x, ∀ G ∈ basis A, {x' | f x' - f x ∈ G} ∈ 𝓝 x :=
begin
  rw continuous_iff_continuous_at,
  apply forall_congr,
  exact λ _, tendsto_into _ _ _,
end

def is_topological_add_group : topological_add_group A :=
  (subgroups_basis.to_ring_filter_basis A).to_add_group_filter_basis.is_topological_group rfl

local attribute [instance] is_topological_add_group

lemma nonarchimedean : topological_add_group.nonarchimedean A :=
begin
  intros U hU,
  rcases mem_nhds_zero.mp hU with ⟨G, G_in, hG⟩,
  exact ⟨⟨G, ⟨is_op A rfl G_in, subgroups_basis.sub_groups G_in⟩⟩, hG⟩
end

section comm_ring

variables {R : Type*} [comm_ring R] {ι : Type*} [inhabited ι] (G : ι → set R) [∀ i, is_add_subgroup $ G i]
  (h_directed : ∀ i j, ∃ k, G k ⊆ G i ∩ G j)
  (h_left_mul : ∀ (x : R) i, ∃ j, x • (G j) ⊆ G i)
  (h_mul : ∀ i, ∃ j, G j * G j ⊆ G i)
include h_directed h_left_mul h_mul

def of_indexed_of_comm : subgroups_basis R :=
{ sets := range G,
  ne_empty := range_ne_empty _,
  directed := begin
    rintros _ _ ⟨i, rfl⟩ ⟨j, rfl⟩,
    rw exists_mem_range,
    tauto
  end,
  sub_groups := begin
    rintro _ ⟨i, rfl⟩,
    apply_instance
  end,
  h_mul := begin
    rintros _ ⟨i, rfl⟩,
    rw exists_mem_range',
    tauto
  end,
  h_left_mul := begin
    rintros x _ ⟨i, rfl⟩,
    rw exists_mem_range',
    rcases h_left_mul x i with ⟨j, h⟩,
    use j,
    rwa [← image_subset_iff, ← smul_set_eq_image]
  end,
  h_right_mul := begin
    rintros x _ ⟨i, rfl⟩,
    rw exists_mem_range',
    rcases h_left_mul x i with ⟨j, h⟩,
    use j,
    simp only [mul_comm],
    rwa [← image_subset_iff, ← smul_set_eq_image]
  end }

end comm_ring
section comm_algebra
open algebra submodule

variables {R : Type*} {B : Type*} [comm_ring R] [comm_ring B] [algebra R B]
  {ι : Type*} [inhabited ι] (M : ι → submodule R B)
  (h_directed : ∀ i j, ∃ k, M k ≤ M i ⊓ M j)
  (h_left_mul : ∀ (a : B) i, ∃ j, a • M j ≤ M i)
  (h_mul      : ∀ i, ∃ j, M j * M j ≤ M i)
include h_directed h_left_mul h_mul


def of_indexed_submodules_of_comm : subgroups_basis B :=
begin
  letI : ∀ i, is_add_subgroup (M i).carrier := λ i, submodule.submodule_is_add_subgroup _,
  apply of_indexed_of_comm _ h_directed,
  { intros x i,
      cases h_left_mul x i with j hj,
      use j,
      erw smul_singleton at hj,
      rw set.smul_set_eq_image,
      exact hj },
    { intro i,
      cases h_mul i with j hj,
      use j,
      rintros _ ⟨x, hx, y, hy, rfl⟩,
    exact hj (mul_mem_mul hx hy) }
end

end comm_algebra

end subgroups_basis
