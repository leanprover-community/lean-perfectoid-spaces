import analysis.topology.uniform_space

import for_mathlib.filter

namespace uniform_space
open uniform_space
variables {α : Type*} [uniform_space α] {β : Type*} [uniform_space β] {γ : Type*} [uniform_space γ]

lemma uniform_continuous.prod.partial1 {f : α × β → γ} (h : uniform_continuous f) :
∀ b, uniform_continuous (λ a, f (a,b)) := λ b, uniform_continuous.comp 
      (uniform_continuous.prod_mk uniform_continuous_id uniform_continuous_const) h

lemma uniform_continuous.prod.partial2 {f : α × β → γ} (h : uniform_continuous f) :
∀ a, uniform_continuous (λ b, f (a,b)) := λ a, uniform_continuous.comp 
      (uniform_continuous.prod_mk uniform_continuous_const uniform_continuous_id) h

instance complete_space.prod [complete_space α] [complete_space β] : complete_space (α × β) :=
{ complete := λ f hf,
    let ⟨x1, hx1⟩ := complete_space.complete $ cauchy_map uniform_continuous_fst hf in
    let ⟨x2, hx2⟩ := complete_space.complete $ cauchy_map uniform_continuous_snd hf in
    ⟨(x1, x2), by rw [nhds_prod_eq, filter.prod_def];
      from filter.le_lift (λ s hs, filter.le_lift' $ λ t ht,
        have H1 : prod.fst ⁻¹' s ∈ f.sets := hx1 hs,
        have H2 : prod.snd ⁻¹' t ∈ f.sets := hx2 ht,
        filter.inter_mem_sets H1 H2)⟩ }

section separation_space

local attribute [instance] separation_setoid

lemma uniform_continuous_quotient {f : quotient (separation_setoid α) → β}
  (hf : uniform_continuous (λx, f ⟦x⟧)) : uniform_continuous f :=
hf

lemma uniform_continuous_quotient_lift
  {f : α → β} {h : ∀a b, (a, b) ∈ separation_rel α → f a = f b}
  (hf : uniform_continuous f) : uniform_continuous (λa, quotient.lift f h a) :=
uniform_continuous_quotient hf

lemma uniformity_quotient :
  @uniformity (quotient (separation_setoid α)) _ = uniformity.map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) :=
rfl

lemma uniform_continuous_quotient_lift₂ [uniform_space γ]
  {f : α → β → γ} {h : ∀a c b d, (a, b) ∈ separation_rel α → (c, d) ∈ separation_rel β → f a c = f b d}
  (hf : uniform_continuous (λp:α×β, f p.1 p.2)) :
  uniform_continuous (λp:_×_, quotient.lift₂ f h p.1 p.2) :=
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    filter.prod_map_map_eq, filter.tendsto_map'_iff, filter.tendsto_map'_iff],
  rwa [uniform_continuous, uniformity_prod_eq_prod, filter.tendsto_map'_iff] at hf
end

lemma separated_of_uniform_continuous {f : α → β} (H : uniform_continuous f) {x y : α} 
(h : x ≈ y) : f x ≈ f y :=
assume _ h', h _ (H h')

lemma eq_of_separated_of_uniform_continuous [separated β] {f : α → β} (H : uniform_continuous f) {x y : α} 
(h : x ≈ y) : f x = f y :=
separated_def.1 (by apply_instance) _ _ $ separated_of_uniform_continuous H h

lemma separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ :=
begin
  split ; intro h,
  { exact ⟨separated_of_uniform_continuous uniform_continuous_fst h,
           separated_of_uniform_continuous uniform_continuous_snd h⟩ },
  { rcases h with ⟨eqv_α, eqv_β⟩,  
    intros r r_in,
    rw uniformity_prod at r_in,
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, H⟩,

    let p_α := λ (p : (α × β) × α × β), ((p.fst).fst, (p.snd).fst),
    let p_β := λ (p : (α × β) × α × β), ((p.fst).snd, (p.snd).snd),    
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α, by simp[p_α, eqv_α r_α r_α_in],
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β, by simp[p_β, eqv_β r_β r_β_in],
    exact H ⟨h_α key_α, h_β key_β⟩ },
end

instance separated.prod [separated α] [separated β] : separated (α × β) := 
separated_def.2 $ assume x y H, prod.ext 
  (eq_of_separated_of_uniform_continuous uniform_continuous_fst H)
  (eq_of_separated_of_uniform_continuous uniform_continuous_snd H)

end separation_space


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