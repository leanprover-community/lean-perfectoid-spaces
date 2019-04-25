import for_mathlib.nonarchimedean.basic

open set filter function lattice add_group_with_zero_nhd

local attribute [instance] set.pointwise_mul_semiring

class is_subgroups_basis {A : Type*} [ring A] {ι : Type*} [inhabited ι] (G : ι → set A) : Prop :=
  [sub_groups : ∀ i, is_add_subgroup $ G i]
  (h_directed : ∀ i j, ∃ k, G k ⊆ G i ∩ G j)
  (h_left_mul : ∀ x i, ∃ j, (λ y : A, x*y) '' (G j) ⊆ G i)
  (h_right_mul : ∀ x i, ∃ j, (λ y : A, y*x) '' (G j) ⊆ G i)
  (h_mul : ∀ i, ∃ j, G j * G j ⊆ G i)

namespace is_subgroups_basis
variables {A : Type*} [ring A] {ι : Type*} [inhabited ι] (G : ι → set A) [is_subgroups_basis G]
include G

instance  (i : ι) : is_add_subgroup (G i) := is_subgroups_basis.sub_groups G i

def to_ring_with_zero_nhd : ring_with_zero_nhd A :=
{ Z :=  (⨅ i, principal (G i)),
  zero_Z :=    assume U H, mem_pure $ let ⟨i, hi⟩ := (mem_infi_range_of_base (h_directed G) U).1 H in
                 hi (is_add_submonoid.zero_mem (G i)),
  sub_Z :=     begin
                 rw tendsto_infi,
                 intro i,
                 rw tendsto_prod_self_iff,
                 intros W W_in,
                 use G i,
                 have ineq : (⨅ (i : ι), principal (G i)) ≤ principal (G i), from infi_le _ _,
                 use ineq (mem_principal_self $ G i),
                 intros x y x_in y_in,
                 exact W_in (is_add_subgroup.sub_mem _ x y x_in y_in)
               end,
  left_mul  := begin
                 intro x₀,
                 rw tendsto_infi,
                 intro i,
                 rw tendsto_principal,
                 rcases h_left_mul G x₀ i with ⟨j, hj⟩,
                 change (λ (y : A), x₀ * y) '' G j ⊆ G i at hj,
                 rw mem_infi_range_of_base (h_directed G),
                 use j,
                 rwa image_subset_iff at hj,
               end,
  right_mul := begin
                intro x₀,
                rw tendsto_infi,
                intro i,
                rw tendsto_principal,
                rcases h_right_mul G x₀ i with ⟨j, hj⟩,
                rw mem_infi_range_of_base (h_directed G),
                use j,
                rwa image_subset_iff at hj,
               end,
  mul_Z :=     begin
                rw tendsto_infi,
                intro i,
                rw tendsto_prod_self_iff,
                intros W W_in,
                rcases h_mul G i with ⟨j, hj⟩,
                use G j,
                have ineq : (⨅ (i : ι), principal (G i)) ≤ principal (G j), from infi_le _ _,
                use ineq (mem_principal_self $ G j),
                intros x y x_in y_in,
                apply W_in,
                apply hj,
                exact ⟨_, x_in, _, y_in, rfl⟩
              end,
  to_ring := ‹ring A› }

local attribute [instance, priority 0] to_ring_with_zero_nhd

lemma nhds_zero (U : set A) : U ∈ nhds (0 : A) ↔ ∃ i, G i ⊆ U :=
begin
  rw nhds_zero_eq_Z,
  change U ∈ (⨅ i, principal (G i)) ↔ _,
  rw mem_infi_range_of_base (h_directed G),
end

lemma mem_nhds_zero (i : ι) : G i ∈ nhds (0 : A) := by { rw nhds_zero, use i}

lemma is_op (i : ι) : is_open (G i) :=
begin
  rw is_open_iff_nhds,
  intros a ha,
  erw [nhds_eq, le_principal_iff, filter.mem_map, filter.mem_infi],
  { rw set.mem_Union,
    use i,
    rw show {x : A | x + a ∈ G i} = G i,
    { ext,
      rw ← (is_add_subgroup.add_mem_cancel_left (G i) ha),
      simp only [iff_self, set.mem_set_of_eq] },
    exact mem_principal_self _ },
  { intros i j,
    cases h_directed G i j with k hk,
    use k,
    split; show principal _ ≤ principal _;
    rw principal_mono;
    refine set.subset.trans hk _,
    { apply set.inter_subset_left },
    { apply set.inter_subset_right } },
  { apply_instance }
end

lemma nonarchimedean : topological_add_group.nonarchimedean A :=
begin
  intros U hU,
  rw nhds_zero at hU,
  cases hU with i hi,
  exact ⟨⟨G i, is_op G i, by apply_instance⟩, hi⟩,
end

section
variables {α : Type*} [add_group α] [topological_space α] [topological_add_group α]
variables (f : α → A) [is_add_group_hom f]

lemma continuous_into (h : ∀ i, is_open (f ⁻¹' (G i))) :
  continuous f :=
begin
  apply topological_add_group.continuous_of_continuous_at_zero f,
  intros U hU,
  rw [is_add_group_hom.map_zero f, nhds_zero] at hU,
  cases hU with i hi,
  rw mem_map_sets_iff,
  refine ⟨f ⁻¹' G i, mem_nhds_sets (h i) _, set.subset.trans _ hi⟩,
  { apply is_add_submonoid.zero_mem },
  { apply image_preimage_subset }
end

variables (g : A → α) [is_add_group_hom g]

-- Following two lines temporarily avoid hell on earth. But there seems to be a real
-- issue with ring_with_nhds related instances...
def tutut := add_monoid.to_has_zero α
local attribute [instance, priority 100] tutut

lemma continuous_from (h : ∀ U : set α, U ∈ (nhds (0 : α)) → ∃ i, G i ⊆ g ⁻¹' U) :
  continuous g :=
begin
  apply topological_add_group.continuous_of_continuous_at_zero g,
  intros U hU,
  rw [is_add_group_hom.map_zero g] at hU,
  cases h U hU with i hi,
  exact mem_sets_of_superset (mem_nhds_zero G i) hi
end
end

variables {B : Type*} [ring B] {J : Type*} [inhabited J] (H : J → set B) [is_subgroups_basis H]
variables (f : A → B) [is_add_group_hom f]

lemma continuous_both (h : ∀ j, ∃ i, G i ⊆ f ⁻¹' (H j)) : continuous f :=
begin
  refine continuous_from G f _,
  intros U U_nhds,
  cases (nhds_zero H U).1 U_nhds with j hj,
  cases h j with i hi,
  exact ⟨i, subset.trans hi $ preimage_mono hj⟩,
end
end is_subgroups_basis
