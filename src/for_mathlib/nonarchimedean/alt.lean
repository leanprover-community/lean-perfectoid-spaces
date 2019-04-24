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

local attribute [instance] to_ring_with_zero_nhd

lemma nhds_zero (U : set A) : U ∈ nhds (0 : A) ↔ ∃ i, G i ⊆ U :=
begin
  rw nhds_zero_eq_Z,
  change U ∈ (⨅ i, principal (G i)) ↔ _,
  rw mem_infi_range_of_base (h_directed G),
end

lemma mem_nhds_zero (i : ι) : G i ∈ nhds (0 : A) := by { rw nhds_zero, use i}

lemma is_open (i : ι) : is_open (G i) :=
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
end is_subgroups_basis
