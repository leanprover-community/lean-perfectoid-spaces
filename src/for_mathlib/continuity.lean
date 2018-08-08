import analysis.topology.continuity

open set filter

variables {α : Type*} [topological_space α] 
variables {β : Type*} [topological_space β]

lemma dense_of_quotient_dense [setoid α] {s : set α} (H : ∀ x, x ∈ closure s) : closure (quotient.mk '' s) = univ :=
begin
  ext x,
  simp,
  rw mem_closure_iff,
  intros U U_op x_in_U,
  let V := quotient.mk ⁻¹' U,
  cases quotient.exists_rep x with y y_x,
  have y_in_V : y ∈ V, by simp [mem_preimage_eq, y_x, x_in_U],
  have V_op : is_open V := U_op,
  have : V ∩ s ≠ ∅ := mem_closure_iff.1 (H y) V V_op y_in_V,
  rcases exists_mem_of_ne_empty this with ⟨w, w_in_V, w_in_range⟩,
  exact ne_empty_of_mem ⟨by tauto, mem_image_of_mem quotient.mk w_in_range⟩
end

-- The following few lemmas are actually not used below, I used to think they would be useful

lemma dense_iff_inter_open {s : set α} : closure s = univ ↔ ∀ U, is_open U → U ≠ ∅ → U ∩ s ≠ ∅ :=
begin
  split ; intro h,
  { intros U U_op U_ne,
    cases exists_mem_of_ne_empty U_ne with x x_in,
    have : x ∈ closure s, by simp[h],
    rw mem_closure_iff at this,
    exact this U U_op x_in },
  { ext x,
    suffices : x ∈ closure s, by simp [this],
    rw mem_closure_iff,
    intros U U_op x_in,
    exact h U U_op (ne_empty_of_mem x_in) },
end

namespace dense_embedding
variables {e : α → β} (de : dense_embedding e)
include de

lemma self_sub_closure_image_preimage_of_open {s : set β} : 
  is_open s → s ⊆ closure (e '' (e ⁻¹' s)) :=
begin
  intros s_op b b_in_s,
  rw [image_preimage_eq_inter_range, mem_closure_iff],
  intros U U_op b_in,
  rw ←inter_assoc,
  have ne_e : U ∩ s ≠ ∅ := ne_empty_of_mem ⟨b_in, b_in_s⟩,
  exact (dense_iff_inter_open.1 de.closure_range) _ (is_open_inter U_op s_op) ne_e
end

lemma closure_image_nhds_of_nhds {s : set α} {a : α} : 
  s ∈ (nhds a).sets → closure (e '' s) ∈ (nhds (e a)).sets :=
begin
  rw [← de.induced a, mem_vmap_sets],
  intro h,
  rcases h with ⟨t, t_nhd, sub⟩,
  rw mem_nhds_sets_iff at t_nhd,
  rcases t_nhd with ⟨U, U_sub, ⟨U_op, e_a_in_U⟩⟩, 
  have := calc e ⁻¹' U ⊆ e⁻¹' t : preimage_mono U_sub
                   ... ⊆ s      : sub,
  have := calc U ⊆ closure (e '' (e ⁻¹' U)) : self_sub_closure_image_preimage_of_open de U_op
             ... ⊆ closure (e '' s)         : closure_mono (image_subset e this),
  
  
  have U_nhd : U ∈ (nhds (e a)).sets := mem_nhds_sets U_op e_a_in_U,
 
  exact (nhds (e a)).upwards_sets U_nhd this,  
end

-- End of useless lemmas

variables {γ : Type*} {δ : Type*} [topological_space δ] {f : γ → α} {g : γ → δ} {h : δ → β}
/--
 γ -f→ α
g↓     ↓e
 δ -h→ β 
-/
lemma tendsto_vmap_nhds_nhds  {d : δ} {a : α} (H : tendsto h (nhds d) (nhds (e a))) (comm : h ∘ g = e ∘ f) : 
  tendsto f (vmap g (nhds d)) (nhds a) :=
begin
  have lim1 : map g (vmap g (nhds d)) ≤ nhds d := map_vmap_le,
  replace lim1 : map h (map g (vmap g (nhds d))) ≤ map h (nhds d) := map_mono lim1,
  rw [filter.map_map, comm, ← filter.map_map, map_le_iff_le_vmap] at lim1,
  have lim2 :  vmap e (map h (nhds d)) ≤  vmap e  (nhds (e a)) := vmap_mono H,
  rw de.induced at lim2,
  exact le_trans lim1 lim2,
end
end dense_embedding