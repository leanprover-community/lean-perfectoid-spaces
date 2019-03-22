import topology.algebra.ring
import ring_theory.subring
import ring_theory.ideal_operations

import for_mathlib.subgroup

universe u

variables {A : Type u} [comm_ring A] [topological_space A] [topological_ring A]

open topological_ring

instance subring_has_zero (R : Type u) [comm_ring R] (S : set R) [HS : is_subring S] : has_zero S :=
⟨⟨0, is_add_submonoid.zero_mem S⟩⟩

instance topological_subring (A₀ : set A) [is_subring A₀] : topological_ring A₀ :=
{ continuous_neg := continuous_subtype_mk _ $ continuous_subtype_val.comp $ continuous_neg A,
  continuous_add := continuous_subtype_mk _ $ continuous_add
    (continuous_fst.comp continuous_subtype_val)
    (continuous_snd.comp continuous_subtype_val),
  continuous_mul := continuous_subtype_mk _ $ continuous_mul
    (continuous_fst.comp continuous_subtype_val)
    (continuous_snd.comp continuous_subtype_val) }

lemma half_nhds {s : set A} (hs : s ∈ (nhds (0 : A))) :
  ∃ V ∈ (nhds (0 : A)), ∀ v w ∈ V, v * w ∈ s :=
begin
  have : ((λa:A×A, a.1 * a.2) ⁻¹' s) ∈ (nhds ((0, 0) : A × A)) :=
    tendsto_mul' (by simpa using hs),
  rw nhds_prod_eq at this,
  rcases filter.mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, filter.inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

lemma continuous_mul_left (a : A) : continuous (λ x, a * x) :=
continuous_mul continuous_const continuous_id

lemma continuous_mul_right (a : A) : continuous (λ x, x * a) :=
continuous_mul continuous_id continuous_const

namespace topological_ring

variables (A)

-- This should be generalised to topological groups, and use `to_additive`.

def open_add_subgroups := { U : set A // is_add_subgroup U ∧ is_open U }

namespace open_add_subgroups
open lattice

@[extensionality]
lemma ext (U V : open_add_subgroups A) : (U = V) ↔ (U.1 = V.1) :=
by cases U; cases V; split; intro h; try {congr}; assumption

variables {A} (U : open_add_subgroups A)

instance : is_add_subgroup U.val := U.2.1

instance : inhabited (open_add_subgroups A) :=
{ default := ⟨set.univ, ⟨by apply_instance, is_open_univ⟩⟩ }

instance : semilattice_inf_top (open_add_subgroups A) :=
{ inf := λ U V, ⟨U.1 ∩ V.1, by apply_instance, is_open_inter U.2.2 V.2.2⟩,
  le := λ U V, U.1 ⊆ V.1,
  le_refl := λ U, set.subset.refl _,
  le_trans := λ U V W h₁ h₂, set.subset.trans h₁ h₂,
  le_antisymm := λ U V h₁ h₂, by rw ext; exact set.subset.antisymm h₁ h₂,
  inf_le_left := λ U V, set.inter_subset_left _ _,
  inf_le_right := λ U V, set.inter_subset_right _ _,
  le_inf := λ U V W hV hW, set.subset_inter hV hW,
  top := default _,
  le_top := λ U, set.subset_univ _, }

lemma is_open_of_open_add_subgroup {s : set A} (h₁ : is_add_subgroup s)
  (h₂ : ∃ U : open_add_subgroups A, U.1 ⊆ s) : is_open s :=
begin
  rw is_open_iff_forall_mem_open,
  intros x hx,
  rcases h₂ with ⟨⟨U, hU, h'U⟩, H⟩,
  use (λ y, y - x) ⁻¹' U,
  split,
  { intros u hu,
    erw set.mem_preimage_eq at hu,
    replace hu := H hu,
    convert is_add_submonoid.add_mem hu hx,
    simp, },
  split,
  { apply continuous_sub continuous_id continuous_const,
    { exact h'U },
    { apply topological_ring.to_topological_add_group } },
  { erw set.mem_preimage_eq,
    convert is_add_submonoid.zero_mem _,
    { simp },
    exact hU.to_is_add_submonoid }
end

end open_add_subgroups

end topological_ring
