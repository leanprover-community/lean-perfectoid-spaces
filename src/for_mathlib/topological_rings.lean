import topology.algebra.ring
import ring_theory.subring
import ring_theory.ideal_operations

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
