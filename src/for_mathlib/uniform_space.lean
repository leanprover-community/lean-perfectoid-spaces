import analysis.topology.uniform_space

namespace uniform_space
open uniform_space
variables {α : Type*} [uniform_space α] {β : Type*} [uniform_space β] {γ : Type*} [uniform_space γ]

open Cauchy set
lemma prod_cauchy {f : filter α} {g : filter β} : cauchy f → cauchy g → cauchy (filter.prod f g)
| ⟨f_proper, hf⟩ ⟨g_proper, hg⟩ := ⟨filter.prod_neq_bot.2 ⟨f_proper, g_proper⟩,
  let p_α := λp:(α×β)×(α×β), (p.1.1, p.2.1), p_β := λp:(α×β)×(α×β), (p.1.2, p.2.2) in
  suffices (f.prod f).vmap p_α ⊓ (g.prod g).vmap p_β ≤ uniformity.vmap p_α ⊓ uniformity.vmap p_β,
    by simpa [uniformity_prod, filter.prod, filter.vmap_inf, filter.vmap_vmap_comp, (∘),
        lattice.inf_assoc, lattice.inf_comm, lattice.inf_left_comm],
  lattice.inf_le_inf (filter.vmap_mono hf) (filter.vmap_mono hg)⟩

def pure_cauchy₂ : α × β → Cauchy α × Cauchy β := λ x, (pure_cauchy x.1, pure_cauchy x.2)

lemma pure_cauchy_dense₂ : ∀x : Cauchy α × Cauchy β, x ∈ closure (range (@pure_cauchy₂ α _ β _)) :=
begin
  intro x,
  dsimp[pure_cauchy₂],
  rw [←prod_range_range_eq, closure_prod_eq],
  simp[prod.ext_iff, pure_cauchy_dense],
end

namespace pure_cauchy
def de := uniform_embedding_pure_cauchy.dense_embedding (@pure_cauchy_dense α _)

lemma prod.de : dense_embedding (λ p : α × β, (pure_cauchy p.1, pure_cauchy p.2)) :=
dense_embedding.prod pure_cauchy.de pure_cauchy.de
end pure_cauchy

end uniform_space

namespace dense_embedding
open filter
variables {α : Type*} [topological_space α]
variables {β : Type*} [topological_space β]

variables {e : α → β} (de : dense_embedding e)

variables {γ : Type*} [uniform_space γ]  [complete_space γ] [separated γ]

lemma continuous_extend_of_cauchy {f : α → γ}  (h : ∀ b : β, cauchy (map f (vmap e $ nhds b))) :
  continuous (de.extend f) :=
continuous_extend de $ λ b, complete_space.complete (h b)

end dense_embedding