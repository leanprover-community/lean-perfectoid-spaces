import analysis.normed_space.basic
import analysis.specific_limits
import for_mathlib.topology

open set metric function

lemma nondiscrete_normed_field.nondiscrete {k  : Type*} [nondiscrete_normed_field k] :
  ¬ discrete_topology k :=
begin
  intro h,
  replace h := discrete_iff_open_singletons.mp h 0,
  rw is_open_iff at h,
  rcases h 0 (mem_singleton 0) with ⟨ε, ε_pos, hε⟩,
  rcases exists_norm_lt_one k with ⟨x₀, x₀_ne, hx₀⟩,
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∥x₀^n∥ < ε,
  { cases tendsto_at_top.mp (tendsto_pow_at_top_nhds_0_of_lt_1 (le_of_lt x₀_ne) hx₀) ε ε_pos with N hN,
    use N,
    simpa [norm_pow] using hN N (le_refl _) },
  rw ball_0_eq at hε,
  specialize hε hn,
  rw [mem_singleton_iff, ← norm_eq_zero, norm_pow] at hε,
  rw pow_eq_zero hε at x₀_ne,
  exact lt_irrefl _ x₀_ne
end
