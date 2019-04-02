import order.filter.lift
import topology.algebra.ring
import ring_theory.algebra
import ring_theory.ideal_operations

import tactic.abel tactic.chain

import for_mathlib.data.set.pointwise_mul
import for_mathlib.subgroup
import for_mathlib.submodule
import for_mathlib.topological_groups

local attribute [instance] set.pointwise_mul_semiring

section
variables (G : Type*) [group G] [topological_space G] [topological_group G]

@[to_additive open_add_subgroup]
def open_subgroup := { U : set G // is_open U ∧ is_subgroup U }

end

namespace open_subgroup
open function lattice
variables {G : Type*} [group G] [topological_space G] [topological_group G]
variables {U V : open_subgroup G}

@[to_additive open_add_subgroup.has_coe]
instance : has_coe (open_subgroup G) (set G) := ⟨λ U, U.1⟩

attribute [to_additive open_add_subgroup.has_coe.equations._eqn_1] open_subgroup.has_coe.equations._eqn_1

@[to_additive open_add_subgroup.has_mem]
instance : has_mem G (open_subgroup G) := ⟨λ g U, g ∈ (U : set G)⟩

attribute [to_additive open_add_subgroup.has_mem.equations._eqn_1] open_subgroup.has_mem.equations._eqn_1

@[to_additive open_add_subgroup.ext']
lemma ext' : (U = V) ↔ ((U : set G) = V) :=
by cases U; cases V; split; intro h; try {congr}; assumption

@[extensionality, to_additive open_add_subgroup.ext]
lemma ext (h : (U : set G) = V) : (U = V) :=
ext'.mpr h

@[to_additive open_add_subgroup.coe_injective]
lemma coe_injective : injective (λ U : open_subgroup G, (U : set G)) :=
λ U V h, ext h

@[to_additive open_add_subgroup.is_add_subgroup]
instance : is_subgroup (U : set G) := U.2.2

variable (U)
protected lemma is_open : is_open (U : set G) := U.2.1

protected lemma one_mem : (1 : G) ∈ U := is_submonoid.one_mem (U : set G)

protected lemma inv_mem {g : G} (h : g ∈ U) : g⁻¹ ∈ U :=
  @is_subgroup.inv_mem G _ U _ g h

protected lemma mul_mem {g₁ g₂ : G} (h₁ : g₁ ∈ U) (h₂ : g₂ ∈ U) : g₁ * g₂ ∈ U :=
  @is_submonoid.mul_mem G _ U _ g₁ g₂ h₁ h₂
variable {U}

instance : inhabited (open_subgroup G) :=
{ default := ⟨set.univ, ⟨is_open_univ, by apply_instance⟩⟩ }

@[to_additive open_add_subgroup.is_open_of_open_add_subgroup]
lemma is_open_of_open_subgroup {s : set G} (h₁ : is_subgroup s)
  (h₂ : ∃ U : open_subgroup G, (U : set G) ⊆ s) : is_open s :=
begin
  rw is_open_iff_forall_mem_open,
  intros x hx,
  rcases h₂ with ⟨⟨U, h₁U, h₂U⟩, H⟩,
  use (λ y, y * x⁻¹) ⁻¹' U,
  split,
  { intros u hu,
    erw set.mem_preimage_eq at hu,
    replace hu := H hu,
    simpa using is_submonoid.mul_mem hu hx },
  split,
  { apply continuous_mul continuous_id continuous_const,
    { exact h₁U },
    { apply_instance } },
  { erw set.mem_preimage_eq,
    simpa using is_submonoid.one_mem _,
    exact h₂U.to_is_submonoid }
end

section
variables {H : Type*} [group H] [topological_space H] [topological_group H]

def prod (U : open_subgroup G) (V : open_subgroup H) : open_subgroup (G × H) :=
⟨(U : set G).prod (V : set H), is_open_prod U.is_open V.is_open, by apply_instance⟩

end

instance : partial_order (open_subgroup G) := partial_order.lift _ coe_injective

instance : semilattice_inf_top (open_subgroup G) :=
{ inf := λ U V, ⟨(U : set G) ∩ V, is_open_inter U.is_open V.is_open, by apply_instance⟩,
  inf_le_left := λ U V, set.inter_subset_left _ _,
  inf_le_right := λ U V, set.inter_subset_right _ _,
  le_inf := λ U V W hV hW, set.subset_inter hV hW,
  top := default _,
  le_top := λ U, set.subset_univ _,
  ..open_subgroup.partial_order }

instance : semilattice_sup_top (open_subgroup G) :=
{ sup := λ U V,
  { val := group.closure ((U : set G) ∪ V),
    property :=
    begin
      have subgrp := _, refine ⟨_, subgrp⟩,
      { apply is_open_of_open_subgroup subgrp,
        exact ⟨U, set.subset.trans (set.subset_union_left _ _) group.subset_closure⟩ },
      { apply_instance }
    end },
  le_sup_left := λ U V, set.subset.trans (set.subset_union_left _ _) group.subset_closure,
  le_sup_right := λ U V, set.subset.trans (set.subset_union_right _ _) group.subset_closure,
  sup_le := λ U V W hU hV, group.closure_subset $ set.union_subset hU hV,
  ..open_subgroup.lattice.semilattice_inf_top }

@[simp] lemma coe_inf : (↑(U ⊓ V) : set G) = (U : set G) ∩ V := rfl

lemma le_iff : U ≤ V ↔ (U : set G) ⊆ V := iff.rfl

end open_subgroup

namespace open_add_subgroup
open lattice
variables {G : Type*} [add_group G] [topological_space G] [topological_add_group G]
variables {U V : open_add_subgroup G}

variable (U)
protected lemma is_open : is_open (U : set G) := U.2.1
attribute [to_additive open_add_subgroup.is_open] open_subgroup.is_open

protected lemma zero_mem : (0 : G) ∈ U := is_add_submonoid.zero_mem (U : set G)
attribute [to_additive open_add_subgroup.zero_mem] open_subgroup.one_mem

protected lemma neg_mem {g : G} (h : g ∈ U) : -g ∈ U :=
  @is_add_subgroup.neg_mem G _ U _ g h
attribute [to_additive open_add_subgroup.neg_mem] open_subgroup.inv_mem

protected lemma add_mem {g₁ g₂ : G} (h₁ : g₁ ∈ U) (h₂ : g₂ ∈ U) : g₁ + g₂ ∈ U :=
  @is_add_submonoid.add_mem G _ U _ g₁ g₂ h₁ h₂
attribute [to_additive open_add_subgroup.add_mem] open_subgroup.mul_mem
variable {U}

section
variables {H : Type*} [add_group H] [topological_space H] [topological_add_group H]

def prod (U : open_add_subgroup G) (V : open_add_subgroup H) : open_add_subgroup (G × H) :=
⟨(U : set G).prod (V : set H), is_open_prod U.is_open V.is_open, by apply_instance⟩
attribute [to_additive open_add_subgroup.prod] open_subgroup.prod
attribute [to_additive open_add_subgroup.prod.equations._eqn_1] open_subgroup.prod.equations._eqn_1

end

instance : inhabited (open_add_subgroup G) :=
{ default := ⟨set.univ, ⟨is_open_univ, by apply_instance⟩⟩ }
attribute [to_additive open_add_subgroup.inhabited] open_subgroup.inhabited

instance : partial_order (open_add_subgroup G) := partial_order.lift _ coe_injective
attribute [to_additive open_add_subgroup.partial_order] open_subgroup.partial_order
attribute [to_additive open_add_subgroup.partial_order.equations._eqn_1] open_subgroup.partial_order.equations._eqn_1

instance : semilattice_inf_top (open_add_subgroup G) :=
{ inf := λ U V, ⟨(U : set G) ∩ V, is_open_inter U.is_open V.is_open, by apply_instance⟩,
  inf_le_left := λ U V, set.inter_subset_left _ _,
  inf_le_right := λ U V, set.inter_subset_right _ _,
  le_inf := λ U V W hV hW, set.subset_inter hV hW,
  top := default _,
  le_top := λ U, set.subset_univ _,
  ..open_add_subgroup.partial_order }
attribute [to_additive open_add_subgroup.lattice.semilattice_inf_top] open_subgroup.lattice.semilattice_inf_top
attribute [to_additive open_add_subgroup.lattice.semilattice_inf_top.equations._eqn_1] open_subgroup.lattice.semilattice_inf_top.equations._eqn_1

instance : semilattice_sup_top (open_add_subgroup G) :=
{ sup := λ U V,
  { val := add_group.closure ((U : set G) ∪ V),
    property :=
    begin
      have subgrp := _, refine ⟨_, subgrp⟩,
      { apply is_open_of_open_add_subgroup subgrp,
        exact ⟨U, set.subset.trans (set.subset_union_left _ _) add_group.subset_closure⟩ },
      { apply_instance }
    end },
  le_sup_left := λ U V, set.subset.trans (set.subset_union_left _ _) group.subset_closure,
  le_sup_right := λ U V, set.subset.trans (set.subset_union_right _ _) group.subset_closure,
  sup_le := λ U V W hU hV, group.closure_subset $ set.union_subset hU hV,
  ..open_add_subgroup.lattice.semilattice_inf_top }
attribute [to_additive open_add_subgroup.lattice.semilattice_sup_top] open_subgroup.lattice.semilattice_sup_top
attribute [to_additive open_add_subgroup.lattice.semilattice_sup_top.equations._eqn_1] open_subgroup.lattice.semilattice_sup_top.equations._eqn_1

@[simp] lemma coe_inf : (↑(U ⊓ V) : set G) = (U : set G) ∩ V := rfl
attribute [to_additive open_add_subgroup.coe_inf] open_subgroup.coe_inf

lemma le_iff : U ≤ V ↔ (U : set G) ⊆ V := iff.rfl
attribute [to_additive open_add_subgroup.le_iff] open_subgroup.le_iff

end open_add_subgroup

/--A topological group is non-archimedean if every open subset
   containing 1 also contains an open subgroup.-/
definition topological_group.nonarchimedean (G : Type*)
  [group G] [topological_space G] [topological_group G] : Prop :=
∀ U ∈ nhds (1 : G), ∃ V : open_subgroup G, (V : set G) ⊆ U

/--A topological additive group is non-archimedean if every open subset
   containing 0 also contains an open additive subgroup.-/
definition topological_add_group.nonarchimedean (G : Type*)
  [add_group G] [topological_space G] [topological_add_group G] : Prop :=
∀ U ∈ nhds (0 : G), ∃ V : open_add_subgroup G, (V : set G) ⊆ U

attribute [to_additive topological_add_group.nonarchimedean] topological_group.nonarchimedean

namespace topological_group
open function set
variables {G₀ : Type*} [group G₀] [topological_space G₀] [topological_group G₀]
variables {G : Type*} [group G] [topological_space G] [topological_group G]
variables (f : G₀ → G) [is_group_hom f]

@[to_additive topological_add_group.nonarchimedean_of_nonarchimedean_open_embedding]
lemma nonarchimedean_of_nonarchimedean_open_embedding
  (emb : embedding f) (hf : is_open (range f)) (h : nonarchimedean G₀) :
  nonarchimedean G :=
begin
  intros U hU,
  cases h (f ⁻¹' U) _ with V hV,
  { refine ⟨⟨f '' V, _, _⟩, _⟩,
    { exact embedding_open emb hf V.is_open },
    { apply_instance },
    { rwa ← set.image_subset_iff at hV } },
  { apply continuous.tendsto (emb.continuous),
    rwa is_group_hom.one f }
end

end topological_group

namespace topological_add_group
namespace nonarchimedean
open topological_ring
variables {R : Type*} [ring R] [topological_space R] [topological_ring R]
variables {S : Type*} [ring S] [topological_space S] [topological_ring S]

lemma left_mul_subset (h : nonarchimedean R) (U : open_add_subgroup R) (r : R) :
  ∃ V : open_add_subgroup R, r • (V : set R) ⊆ U :=
begin
  let V : open_add_subgroup R := ⟨_, _, _⟩,
  { use V,
    intros x hx,
    rw set.mem_smul_set at hx,
    rcases hx with ⟨y, hy, rfl⟩,
    exact hy },
  { apply continuous_mul continuous_const continuous_id,
    exact U.is_open,
    apply_instance },
  { refine {..}; intros,
    { show r * 0 ∈ U, simpa using U.zero_mem },
    { show r * (_ + _) ∈ U, rw left_distrib, apply U.add_mem, assumption' },
    { show r * _ ∈ U, rw mul_neg_eq_neg_mul_symm, apply U.neg_mem, assumption } },
end

lemma prod_subset (hR : nonarchimedean R) (hS : nonarchimedean S) :
  ∀ U ∈ nhds (0 : R × S), ∃ (V : open_add_subgroup R) (W : open_add_subgroup S),
    (V : set R).prod (W : set S) ⊆ U :=
begin
  intros U hU,
  erw [nhds_prod_eq, filter.mem_prod_iff] at hU,
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩,
  cases hR _ hU₁ with V hV,
  cases hS _ hU₂ with W hW,
  use [V, W],
  refine set.subset.trans (set.prod_mono _ _) h; assumption
end

lemma prod_self_subset (hR : nonarchimedean R) :
  ∀ U ∈ nhds (0 : R × R), ∃ (V : open_add_subgroup R), (V : set R).prod (V : set R) ⊆ U :=
begin
  intros U hU,
  rcases prod_subset hR hR U hU with ⟨V, W, h⟩,
  use V ⊓ W,
  refine set.subset.trans (set.prod_mono _ _) ‹_›; simp
end

lemma prod (hR : nonarchimedean R) (hS : nonarchimedean S) :
  nonarchimedean (R × S) :=
begin
  intros U hU,
  rcases prod_subset hR hS U hU with ⟨V, W, h⟩,
  refine ⟨V.prod W, ‹_›⟩
end

lemma mul_subset (h : nonarchimedean R) (U : open_add_subgroup R) :
  ∃ V : open_add_subgroup R, (V : set R) * V ⊆ U :=
begin
  rcases prod_self_subset h _ _ with ⟨V, H⟩,
  use V,
  work_on_goal 0 {
    rwa [set.pointwise_mul_eq_image, set.image_subset_iff] },
  apply mem_nhds_sets (continuous_mul' _ U.is_open),
  simpa only [prod.fst_zero, prod.snd_zero, set.mem_preimage_eq, mul_zero] using U.zero_mem
end

end nonarchimedean
end topological_add_group

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
(left_mul (x₀ : α) : tendsto (λ x : α, x₀ * x) Z Z)
(right_mul (x₀ : α) : tendsto (λ x : α, x * x₀) Z Z)
(mul_Z {} : tendsto (λp:α×α, p.1 * p.2) (Z.prod Z) Z)

end

namespace ring_with_zero_nhd
variables (α : Type*) [ring_with_zero_nhd α]
open filter add_group_with_zero_nhd function
local notation `Z` := add_group_with_zero_nhd.Z

instance to_add_group_with_zero_nhd {α :Type*} [ring_with_zero_nhd α] :
  add_group_with_zero_nhd α :=
{..‹ring_with_zero_nhd α›}

instance : topological_space α := by apply_instance

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
  (h_mul : ∀ i, ∃ j, G j * G j ⊆ G i)
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
                apply hj,
                exact ⟨_, x_in, _, y_in, rfl⟩
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
  change U ∈ (⨅ i, principal (G i)) ↔ _,
  rw mem_infi_range_of_base h_directed,
end

variables {G h_directed h_left_mul h_right_mul h_mul}

lemma of_subgroups.is_open (i : ι) :
  @is_open A (topology_of_subgroups G h_directed h_left_mul h_right_mul h_mul) (G i) :=
begin
  letI rnz := (of_subgroups _ h_directed h_left_mul h_right_mul h_mul),
  rw is_open_iff_nhds,
  intros a ha,
  erw [nhds_eq, le_principal_iff, filter.mem_map, filter.mem_infi],
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

lemma of_subgroups.nonarchimedean :
  @topological_add_group.nonarchimedean A _
  (topology_of_subgroups G h_directed h_left_mul h_right_mul h_mul)
  (by letI := of_subgroups G h_directed h_left_mul h_right_mul h_mul; apply_instance) :=
begin
  intros U hU,
  rw of_subgroups.nhds_zero at hU,
  cases hU with i hi,
  exact ⟨⟨G i, of_subgroups.is_open i, by apply_instance⟩, hi⟩,
end

section
variables {α : Type*} [add_group α] [topological_space α] [topological_add_group α]
variables (f : α → A) [is_add_group_hom f]

lemma of_subgroups.continuous (h : ∀ i, is_open (f ⁻¹' (G i))) :
  @continuous _ _ _ (topology_of_subgroups G h_directed h_left_mul h_right_mul h_mul) f :=
begin
  letI rnz := (of_subgroups _ h_directed h_left_mul h_right_mul h_mul),
  apply topological_add_group.continuous_of_continuous_at_zero f,
  intros U hU,
  rw [is_add_group_hom.zero f, of_subgroups.nhds_zero] at hU,
  cases hU with i hi,
  rw mem_map_sets_iff,
  refine ⟨f ⁻¹' G i, mem_nhds_sets (h i) _, set.subset.trans _ hi⟩,
  { apply is_add_submonoid.zero_mem },
  { apply image_preimage_subset }
end

end

end

section comm_ring

variables {A : Type*} [comm_ring A] {ι : Type*} [inhabited ι] (G : ι → set A) [∀ i, is_add_subgroup $ G i]
  (h_directed : ∀ i j, ∃ k, G k ⊆ G i ∩ G j)
  (h_left_mul : ∀ (x : A) i, ∃ j, x • (G j) ⊆ G i)
  (h_mul : ∀ i, ∃ j, G j * G j ⊆ G i)
include h_directed h_left_mul h_mul

def of_subgroups_comm : ring_with_zero_nhd A :=
of_subgroups G h_directed
(by simpa only [set.smul_set_eq_image] using h_left_mul)
(by simpa only [set.smul_set_eq_image, mul_comm] using h_left_mul)
h_mul

def topology_of_subgroups_comm : topological_space A :=
topology_of_subgroups G h_directed
(by simpa only [set.smul_set_eq_image] using h_left_mul)
(by simpa only [set.smul_set_eq_image, mul_comm] using h_left_mul)
h_mul

variables {G h_directed h_left_mul h_mul}

lemma of_subgroups_comm.is_open (i : ι) :
  @is_open A (topology_of_subgroups_comm G h_directed h_left_mul h_mul) (G i) :=
of_subgroups.is_open i

section
variables {α : Type*} [add_group α] [topological_space α] [topological_add_group α]
variables (f : α → A) [is_add_group_hom f]

lemma of_subgroups_comm.continuous (h : ∀ i, is_open (f ⁻¹' (G i))) :
  @continuous _ _ _ (topology_of_subgroups_comm G h_directed h_left_mul h_mul) f :=
of_subgroups.continuous f h

end

end comm_ring

section comm_algebra
open algebra

variables {R : Type*} {A: Type*} [comm_ring R] [comm_ring A] [algebra R A]
  {ι : Type*} [inhabited ι] (M : ι → submodule R A)
  (h_directed : ∀ i j, ∃ k, M k ≤ M i ⊓ M j)
  (h_left_mul : ∀ (a : A) i, ∃ j, a • M j ≤ M i)
  (h_mul      : ∀ i, ∃ j, M j * M j ≤ M i)
include h_directed h_left_mul h_mul

def of_submodules_comm : ring_with_zero_nhd A :=
of_subgroups_comm (λ i, (M i : set A)) h_directed
begin
  intros x i,
  cases h_left_mul x i with j hj,
  use j,
  erw submodule.smul_singleton at hj,
  erw set.smul_set_eq_image,
  exact hj
end
begin
  intro i,
  cases h_mul i with j hj,
  use j,
  rintros _ ⟨x, hx, y, hy, rfl⟩,
  apply hj,
  exact mul_mem_mul hx hy,
end

def topology_of_submodules_comm : topological_space A :=
topology_of_subgroups_comm (λ i, (M i : set A)) h_directed
begin
  intros x i,
  cases h_left_mul x i with j hj,
  use j,
  erw submodule.smul_singleton at hj,
  erw set.smul_set_eq_image,
  exact hj
end
begin
  intro i,
  cases h_mul i with j hj,
  use j,
  rintros _ ⟨x, hx, y, hy, rfl⟩,
  apply hj,
  exact mul_mem_mul hx hy,
end

lemma of_submodules_comm.nhds_zero (U : set A) :
  U ∈ @nhds A (topology_of_submodules_comm _ h_directed h_left_mul h_mul)
    (0 : A) ↔ ∃ i, (M i : set A) ⊆ U :=
of_subgroups.nhds_zero _ _ _ _ _ _

variables {M h_directed h_left_mul h_mul}

lemma of_submodules_comm.is_open (i : ι) :
  @is_open A (topology_of_submodules_comm M h_directed h_left_mul h_mul) (M i) :=
by convert of_subgroups_comm.is_open i

lemma of_submodules_comm.nonarchimedean :
  @topological_add_group.nonarchimedean A _
  (topology_of_submodules_comm M h_directed h_left_mul h_mul)
  (by letI := of_submodules_comm M h_directed h_left_mul h_mul; apply_instance) :=
of_subgroups.nonarchimedean

section
variables {α : Type*} [add_group α] [topological_space α] [topological_add_group α]
variables (f : α → A) [is_add_group_hom f]

lemma of_submodules_comm.continuous (h : ∀ i, is_open (f ⁻¹' (M i))) :
  @continuous _ _ _ (topology_of_submodules_comm M h_directed h_left_mul h_mul) f :=
of_subgroups.continuous f h

end

end comm_algebra

namespace submodule
variables {R : Type*} {M : Type*} [comm_ring R]
variables [add_comm_group M] [topological_space M] [topological_add_group M] [module R M]

lemma is_open_of_open_submodule {P : submodule R M}
  (h : ∃ U : submodule R M, is_open (U : set M) ∧ U ≤ P) : is_open (P : set M) :=
begin
  letI H : is_add_subgroup (P : set M) := by apply_instance,
  apply open_add_subgroup.is_open_of_open_add_subgroup H,
  rcases h with ⟨U, h₁, h₂⟩,
  exact ⟨⟨U, h₁, by apply_instance⟩, h₂⟩
end

end submodule

namespace ideal
open lattice
variables {R : Type*} [comm_ring R]

def adic_topology (I : ideal R) : topological_space R :=
topology_of_submodules_comm
  (λ n : ℕ, I^n)
  (by { intros i j, use (i + j), rw pow_add, exact mul_le_inf })
  (by { intros r i, use i, exact le_trans mul_le_inf inf_le_right })
  (by { intro i, use i, exact le_trans mul_le_inf inf_le_left })

def adic_ring (I : ideal R) := R

namespace adic_ring
variable (I : ideal R)

instance : ring_with_zero_nhd I.adic_ring :=
by delta adic_ring; exact
of_submodules_comm
  (λ n : ℕ, I^n)
  (by { intros i j, use (i + j), rw pow_add, exact mul_le_inf })
  (by { intros r i, use i, exact le_trans mul_le_inf inf_le_right })
  (by { intro i, use i, exact le_trans mul_le_inf inf_le_left })

instance : topological_space I.adic_ring := by apply_instance

instance : topological_ring I.adic_ring := by apply_instance

lemma nonarchimedean : topological_add_group.nonarchimedean I.adic_ring :=
of_submodules_comm.nonarchimedean

end adic_ring

section
variables [topological_space R] [topological_ring R]

lemma is_open_of_open_subideal {I : ideal R}
  (h : ∃ U : ideal R, is_open (U : set R) ∧ U ≤ I) : is_open (I : set R) :=
submodule.is_open_of_open_submodule h

end

end ideal




#exit

variables {R : Type*} [comm_ring R]

variables [topological_space R] [topological_ring R]

lemma is_ideal_adic.nonarchimedean {J : ideal R} (h : is-J-adic) :
  nonarchimedean R := by convert adic_ring.nonarchimedean J

lemma is_adic.nonarchimedean (h : is_adic R) :
  nonarchimedean R :=
begin
  rcases h with ⟨J, hJ⟩,
  exact hJ.nonarchimedean
end
