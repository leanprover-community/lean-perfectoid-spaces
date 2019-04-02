import tactic.abel
import order.filter
import topology.algebra.group
import topology.algebra.ring
import order.filter.lift

import tactic.where
/-
section bases
open filter set
variables {α : Type*} {ι : Type*} {s : ι → set α} [inhabited ι]
lemma generate_eq_of_base (H : ∀ i j, ∃ k, s k ⊆ s i ∩ s j) (U : set α) :
  U ∈ generate (range s) ↔ ∃ i, s i ⊆ U :=
begin
  split ; intro h,
  { induction h with U U_in U V U_gen UV U_union U V U_gen V_gen U_union V_union,
    { rcases U_in with ⟨i, rfl⟩,
      use i },
    { use default ι,
      exact (univ_mem_sets : univ ∈ principal (s $ default ι))},
    { cases U_union with i Ui,
      use i,
      exact subset.trans Ui UV },
    { cases U_union with i Ui,
      cases V_union with j Vj,
      cases H i j with k k_sub,
      use k,
      cases subset_inter_iff.1 k_sub with ki kj,
      exact subset_inter_iff.2 ⟨subset.trans ki Ui, subset.trans kj Vj⟩ }},
  { cases h with i Ui,
    exact generate_sets.superset (generate_sets.basic $ mem_range_self i) Ui },
end

lemma mem_infi_range_of_base (H : ∀ i j, ∃ k, s k ⊆ s i ∩ s j) (U : set α) :
  U ∈ (⨅ i, principal (s i)) ↔  ∃ i, s i ⊆ U :=
begin
  rw mem_infi,
  { split,
    { exact λ ⟨_, ⟨i, rfl⟩, Ui⟩, ⟨i, Ui⟩ },
    { rintro ⟨i, Ui⟩,
      rw mem_Union,
      use [i, Ui] } },
  { rintros i j,
    cases H i j with k k_sub,
    use k,
    split ; apply principal_mono.2 ; simp [set.subset_inter_iff.1 k_sub] },
  { apply_instance }
end

lemma generate_eq_infi (H : ∀ i j, ∃ k, s k ⊆ s i ∩ s j) :
  generate (range s) = ⨅ i, principal (s i) :=
by ext t ; rw [generate_eq_of_base H, mem_infi_range_of_base H]
end bases


namespace add_group_with_zero_nhd
variables (α : Type*) [add_group_with_zero_nhd α]
open filter

lemma nhds_eq' (a : α) : nhds a = map (λx, a + x) (Z α) :=
by convert nhds_eq a ; ext ; simp
end add_group_with_zero_nhd

section
universe u
open filter

class ring_with_zero_nhd (α : Type u) extends ring α:=
(Z : filter α)
(zero_Z {} : pure 0 ≤ Z)
(sub_Z {} : tendsto (λp:α×α, p.1 - p.2) (Z.prod Z) Z)
(left_mul (x₀ : α) : tendsto (λ x : α, x₀*x) Z Z)
(right_mul (x₀ : α) : tendsto (λ x : α, x*x₀) Z Z)
(mul_Z {} : tendsto (λp:α×α, p.1*p.2) (Z.prod Z) Z)
end

namespace ring_with_zero_nhd
variables (α : Type*) [ring_with_zero_nhd α]
open filter add_group_with_zero_nhd function
local notation `Z` := add_group_with_zero_nhd.Z

instance to_add_group_with_zero_nhd {α :Type*} [ring_with_zero_nhd α] :
  add_group_with_zero_nhd α :=
{..‹ring_with_zero_nhd α›}

instance : topological_space α :=
by apply_instance

instance : topological_ring α :=
begin
  refine {..add_group_with_zero_nhd.topological_add_group, ..},
  rw continuous_iff_continuous_at,
  rintro ⟨x₀, y₀⟩,
  rw [continuous_at, nhds_prod_eq, nhds_eq', nhds_eq', nhds_eq', filter.prod_map_map_eq,
      tendsto_map'_iff],
  suffices :
  tendsto ((λ (x : α), x + x₀ * y₀) ∘ (λ (p : α × α), p.fst + p.snd) ∘
            (λ (p : α × α), (p.1*y₀ + x₀*p.2, p.1*p.2)))
    (filter.prod (Z α) $ Z α)
    (map (λ (x : α), x + x₀ * y₀) $ Z α),
  { convert this using 1,
    { ext, simp only [comp_app],
      repeat { rw mul_add <|> rw add_mul },
      abel },
    simp },
  refine tendsto.comp _ tendsto_map,
  refine tendsto.comp _ add_Z,
  apply tendsto.prod_mk _ ring_with_zero_nhd.mul_Z,
  { change tendsto ((λ p : α × α, p.1 + p.2) ∘ (λ (x : α × α), (x.fst * y₀, x₀ * x.snd))) (filter.prod (Z α) (Z α)) (Z α),
    refine tendsto.comp _ add_Z,
    apply tendsto.prod_mk,
    { exact tendsto_fst.comp (ring_with_zero_nhd.right_mul y₀) },
    { exact tendsto_snd.comp (ring_with_zero_nhd.left_mul  x₀) } },
end

end ring_with_zero_nhd

section
open filter set lattice add_group_with_zero_nhd
variables {A : Type*} [ring A] {ι : Type*} [inhabited ι] (G : ι → set A) [∀ i, is_add_subgroup $ G i]
  (h_directed : ∀ i j, ∃ k, G k ⊆ G i ∩ G j)
  (h_left_mul : ∀ x i, ∃ j, (λ y : A, x*y) '' (G j) ⊆ G i)
  (h_right_mul : ∀ x i, ∃ j, (λ y : A, y*x) '' (G j) ⊆ G i)
  (h_mul : ∀ i, ∃ j, (λ x : A × A, x.1*x.2) '' (set.prod (G j) (G j)) ⊆ G i)
include h_directed h_left_mul h_right_mul h_mul

def of_subgroups : ring_with_zero_nhd A :=
{ Z :=  (⨅ i, principal (G i)),
  zero_Z :=    assume U H, mem_pure $ let ⟨i, hi⟩ := (mem_infi_range_of_base h_directed U).1 H in
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
                 rcases h_left_mul x₀ i with ⟨j, hj⟩,
                 rw mem_infi_range_of_base h_directed,
                 use j,
                 rwa image_subset_iff at hj,
               end,
  right_mul := begin
                intro x₀,
                rw tendsto_infi,
                intro i,
                rw tendsto_principal,
                rcases h_right_mul x₀ i with ⟨j, hj⟩,
                rw mem_infi_range_of_base h_directed,
                use j,
                rwa image_subset_iff at hj,
               end,
  mul_Z :=     begin
                rw tendsto_infi,
                intro i,
                rw tendsto_prod_self_iff,
                intros W W_in,
                rcases h_mul i with ⟨j, hj⟩,
                use G j,
                have ineq : (⨅ (i : ι), principal (G i)) ≤ principal (G j), from infi_le _ _,
                use ineq (mem_principal_self $ G j),
                intros x y x_in y_in,
                apply W_in,
                rw image_subset_iff at hj,
                exact hj (⟨x_in, y_in⟩ : (x, y) ∈ set.prod (G j) (G j)),
              end,
  to_ring := ‹ring A› }

def topology_of_subgroups : topological_space A :=
@ring_with_zero_nhd.topological_space A
  (of_subgroups _ h_directed h_left_mul h_right_mul h_mul)

lemma of_subgroups.nhds_zero (U : set A) :
  U ∈ @nhds A (topology_of_subgroups _ h_directed h_left_mul h_right_mul h_mul)
    (0 : A) ↔ ∃ i, G i ⊆ U :=
begin
  letI rnz := (of_subgroups _ h_directed h_left_mul h_right_mul h_mul),
  rw @add_group_with_zero_nhd.nhds_zero_eq_Z A (@ring_with_zero_nhd.to_add_group_with_zero_nhd A rnz),
  change  U ∈ (⨅ i, principal (G i)) ↔ _,
  rw mem_infi_range_of_base h_directed,
end

lemma of_subgroups.is_open (i : ι) :
  @is_open A (topology_of_subgroups _ h_directed h_left_mul h_right_mul h_mul) (G i) :=
begin
  letI rnz := (of_subgroups _ h_directed h_left_mul h_right_mul h_mul),
  rw is_open_iff_nhds,
  intros a ha,
  rw nhds_eq,
  rw le_principal_iff,
  rw filter.mem_map,
  erw filter.mem_infi,
  { rw set.mem_Union,
    use i,
    rw show {x : A | x + a ∈ G i} = G i,
    { ext g,
      split; intro h,
      { rw ← (is_add_subgroup.add_mem_cancel_left (G i) ha),
        assumption },
      { rw ← (is_add_subgroup.add_mem_cancel_left (G i) ha) at h,
        assumption } },
    exact mem_principal_self _ },
  { intros i j,
    cases h_directed i j with k hk,
    use k,
    split; show principal _ ≤ principal _;
    rw principal_mono;
    refine set.subset.trans hk _,
    { apply set.inter_subset_left },
    { apply set.inter_subset_right } },
  { apply_instance }
end

end

section comm_ring

variables {A : Type*} [comm_ring A] {ι : Type*} [inhabited ι] (G : ι → set A) [∀ i, is_add_subgroup $ G i]
  (h_directed : ∀ i j, ∃ k, G k ⊆ G i ∩ G j)
  (h_left_mul : ∀ x i, ∃ j, (λ y : A, x*y) '' (G j) ⊆ G i)
  (h_mul : ∀ i, ∃ j, (λ x : A × A, x.1*x.2) '' (set.prod (G j) (G j)) ⊆ G i)
include h_directed h_left_mul h_mul

def of_subgroups_comm : ring_with_zero_nhd A :=
of_subgroups G h_directed h_left_mul (by simpa only [mul_comm]) h_mul

def topology_of_subgroups_comm : topological_space A :=
topology_of_subgroups G h_directed h_left_mul (by simpa only [mul_comm]) h_mul

end comm_ring
-/
