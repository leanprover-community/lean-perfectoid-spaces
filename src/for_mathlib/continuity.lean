import analysis.topology.continuity

open set

variables {α : Type*} [topological_space α] [setoid α]

lemma dense_of_quotient_dense {s : set α} (H : ∀ x, x ∈ closure s) : closure (quotient.mk '' s) = univ :=
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