import topology.uniform_space.cauchy
import topology.algebra.uniform_group
import for_mathlib.topological_groups

open filter set

local infixr ` ×ᶠ `:51 := filter.prod
local notation `𝓤` := uniformity
local notation `𝓝` x:70 := nhds x

section
open tactic
meta def clean_step : tactic unit :=
do tgt ← target,
   match tgt with
   | `(%%a → %%b) := `[intros]
   | `(%%a ↔ %%b) := match a with
                     | `(%%c → %%d) := if c.has_var then `[apply imp_congr] else `[apply forall_congr]
                     | `(Exists %%c) := `[apply exists_congr]
                     | _ := `[exact iff.rfl]
                     end
   | _ := fail "Goal is not a forall, implies or iff"
   end

meta def tactic.interactive.clean_iff : tactic unit := do repeat clean_step
end

variables (α : Type*) [uniform_space α] [add_group α] [uniform_add_group α]

lemma add_group_filter_basis.cauchy_iff {B : add_group_filter_basis α}
  (h : uniform_space.to_topological_space α = B.topology) {F : filter α} :
  cauchy F ↔ F ≠ ⊥ ∧ ∀ U ∈ B, ∃ M ∈ F, ∀ x y ∈ M, y - x ∈ U :=
begin
  suffices : F ×ᶠ F ≤ 𝓤 α ↔ ∀ U ∈ B, ∃ M ∈ F, ∀ x y ∈ M, y - x ∈ U,
    by split ; rintros ⟨h', h⟩ ; refine ⟨h', _⟩ ; [rwa ← this, rwa this],
  rw [uniformity_eq_comap_nhds_zero α, ← map_le_iff_le_comap],
  change tendsto _ _ _ ↔ _,
  rw [B.nhds_zero_eq h, filter_basis.tendsto_into],
  simp only [mem_prod_same_iff],
  clean_iff,
  rw [subset_def, prod.forall],
  clean_iff,
  rw [prod_mk_mem_set_prod_eq],
  tauto!
end

lemma test {α : Type*} [has_sub α] (S T : set $ set α) :
 (∀ {V : set α}, V ∈ S → (∃ (t : set α) (H : t ∈ T), set.prod t t ⊆ (λ (x : α × α), x.snd - x.fst) ⁻¹' V)) ↔
    ∀ (U : set α), U ∈ S → (∃ (M : set α) (H : M ∈ T), ∀ (x y : α), x ∈ M → y ∈ M → y - x ∈ U) :=
begin
  clean_iff,
  rw [subset_def, prod.forall],
  clean_iff,
  rw [set.prod_mk_mem_set_prod_eq],
  tauto!
end
