import topology.algebra.ordered

import for_mathlib.linear_ordered_comm_group
import for_mathlib.filter
import for_mathlib.topology

local attribute [instance, priority 0] classical.decidable_linear_order
local notation `𝓝` x: 70 := nhds x
variables {Γ : Type*} [linear_ordered_comm_group Γ]

section with_zero_topology
open topological_space filter set

variables (Γ)
def with_zero.nhds_fun : with_zero Γ → filter (with_zero Γ) :=
  (λ x : with_zero Γ, if x = 0 then ⨅ (γ₀ : Γ), principal {γ | γ < γ₀} else pure x)

def with_zero.topological_space : topological_space (with_zero Γ) :=
topological_space.mk_of_nhds (with_zero.nhds_fun Γ)

local attribute [instance] with_zero.topological_space

lemma with_zero.directed_lt : directed (≥) (λ (γ₀ : Γ), principal {γ : with_zero Γ | γ < ↑γ₀}) :=
begin
  intros γ₁ γ₂,
  use min γ₁ γ₂,
  split,
  { change  principal {γ : with_zero Γ | γ < ↑(min γ₁ γ₂)} ≤ principal {γ : with_zero Γ | γ < ↑γ₁},
    rw [principal_mono, with_zero.coe_min],
    intros x x_in,
    calc x < min ↑γ₁ ↑γ₂ : x_in
        ... ≤ γ₁ : min_le_left _ _ },
  { change  principal {γ : with_zero Γ | γ < ↑(min γ₁ γ₂)} ≤ principal {γ : with_zero Γ | γ < ↑γ₂},
    rw [principal_mono, with_zero.coe_min],
    intros x x_in,
    calc x < min ↑γ₁ ↑γ₂ : x_in
        ... ≤ γ₂ : min_le_right _ _ }
end

lemma with_zero.pure_le_nhds_fun : pure ≤ with_zero.nhds_fun Γ :=
begin
  intro x,
  induction x using with_zero.cases_on ; simp [with_zero.nhds_fun]
end

lemma with_zero.nhds_fun_ok : ∀ (x : with_zero Γ) (s ∈ with_zero.nhds_fun Γ x),
  (∃ t ∈ with_zero.nhds_fun Γ x, t ⊆ s ∧ ∀ y ∈ t, s ∈ with_zero.nhds_fun Γ y) :=
begin
  intros x U U_in,
  induction x using with_zero.cases_on,
  { simp [with_zero.nhds_fun] at U_in ⊢,
    rw [mem_infi (with_zero.directed_lt Γ) ⟨1⟩, mem_Union] at U_in,
    cases U_in with γ₀ h,
    use {γ : with_zero Γ | γ < ↑γ₀},
    rw mem_principal_sets at h,
    split,
    { apply mem_infi_sets γ₀,
      rw mem_principal_sets},
    { refine ⟨h, _⟩,
      intros x x_in,
      induction x using with_zero.cases_on ; simp,
      { apply mem_infi_sets γ₀,
        rwa mem_principal_sets },
      { exact h x_in } } },
  { simp [with_zero.nhds_fun] at *,
    use {x},
    refine ⟨mem_singleton _, singleton_subset_iff.2 U_in, _⟩,
    intros y y_in,
    rw mem_singleton_iff at y_in,
    rw y_in,
    simpa }
end

variables  {Γ}
lemma with_zero.nhds_coe (γ : Γ) : nhds (γ : with_zero Γ) = pure (γ : with_zero Γ) :=
nhds_mk_of_nhds (with_zero.nhds_fun Γ) γ (with_zero.pure_le_nhds_fun Γ) (with_zero.nhds_fun_ok Γ)

lemma with_zero.singleton_nhds (γ : Γ) : ({γ} : set $ with_zero Γ) ∈ nhds (γ : with_zero Γ) :=
by simp [with_zero.nhds_coe γ]

lemma with_zero.nhds_zero_mem (U : set $ with_zero Γ) : U ∈ nhds (0 : with_zero Γ) ↔ ∃ γ₀ : Γ,  {x : with_zero Γ | x < γ₀} ⊆ U :=
begin
  rw nhds_mk_of_nhds (with_zero.nhds_fun Γ) 0 (with_zero.pure_le_nhds_fun Γ) (with_zero.nhds_fun_ok Γ),
  simp [with_zero.nhds_fun],
  rw mem_infi (with_zero.directed_lt Γ) ⟨1⟩,
  { split,
    { rintro ⟨_, ⟨γ₀, rfl⟩, H⟩,
      rw mem_principal_sets at H,
      use [γ₀, H] },
    { rintro ⟨γ₀, H⟩,
      rw mem_Union,
      use γ₀,
      rwa mem_principal_sets } }
end

lemma with_zero.nhds_zero (γ : Γ) : {x : with_zero Γ | x < γ} ∈ nhds (0 : with_zero Γ) :=
by { rw with_zero.nhds_zero_mem, use γ }

variable (Γ)

def with_zero.ordered_topology : ordered_topology (with_zero Γ) :=
{ is_closed_le' :=
  begin
    show is_open {p : with_zero Γ × with_zero Γ | ¬p.fst ≤ p.snd},
    simp only [not_le],
    rw is_open_iff_mem_nhds,
    rintros ⟨a,b⟩ hab,
    change b < a at hab,
    cases with_zero.coe_of_gt hab with γ H,
    rw [nhds_prod_eq, mem_prod_iff, H],
    induction b using with_zero.cases_on,
    { use [{γ}, with_zero.singleton_nhds γ, {x : with_zero Γ | x < γ}, with_zero.nhds_zero γ],
      intros p p_in,
      cases mem_prod.1 p_in with h1 h2,
      rw mem_singleton_iff at h1,
      change p.2 < p.1,
      rwa h1 },
    { use [{γ}, with_zero.singleton_nhds γ, {b}, with_zero.singleton_nhds b],
      intros p p_in,
      cases mem_prod.1 p_in with h1 h2,
      rw mem_singleton_iff at h1 h2,
      change p.2 < p.1,
      rwa [h1, h2, ← H] }
  end }

local attribute [instance] with_zero.ordered_topology

lemma with_zero.t2_space : t2_space (with_zero Γ) := ordered_topology.to_t2_space
local attribute [instance] with_zero.t2_space

lemma with_zero.regular_space : regular_space (with_zero Γ) :=
begin
  haveI : t1_space (with_zero Γ) := t2_space.t1_space,
  split,
  intros s x s_closed x_not_in_s,
  with_zero_cases x,
  { refine ⟨s, _, subset.refl _, _⟩,
    { rw is_open_iff_mem_nhds,
      intros y hy,
      with_zero_cases y,
      simpa [with_zero.nhds_coe] },
    { rw inf_eq_bot_iff,
      use -s,
      simp only [exists_prop, mem_principal_sets],
      split,
      exact mem_nhds_sets (by rwa is_open_compl_iff) (by rwa mem_compl_iff),
      exact ⟨s, subset.refl s, by simp⟩ } },
  { simp only [inf_eq_bot_iff, exists_prop, mem_principal_sets],
    exact ⟨-{x}, is_open_compl_iff.mpr is_closed_singleton, by rwa subset_compl_singleton_iff,
          {x}, with_zero.singleton_nhds x, -{x}, by simp [subset.refl]⟩ }
end

def with_zero.zero_filter_basis : filter_basis (with_zero Γ) :=
{ sets := range (λ γ : Γ, {x : with_zero Γ | x < γ}),
  ne_empty := range_ne_empty.mpr ⟨1⟩,
  directed := begin
    intros s t hs ht,
    rw mem_range at hs ht,
    rcases hs with ⟨γs, rfl⟩,
    rcases ht with ⟨γt, rfl⟩,
    simp only [exists_prop, mem_range],
    rcases with_zero.directed_lt Γ γs γt with ⟨γ, hs, ht⟩,
    change  principal {g : with_zero Γ | g < ↑γ} ≤ principal {g : with_zero Γ | g < ↑γt} at ht,
    change  principal {g : with_zero Γ | g < ↑γ} ≤ principal {g : with_zero Γ | g < ↑γs} at hs,
    rw [le_principal_iff, mem_principal_sets] at hs ht,
    use [{x : with_zero Γ | x < γ}, γ, rfl, subset_inter_iff.mpr ⟨hs, ht⟩]
  end}

variable {Γ}

def with_zero.coe_filter_basis (x : Γ) : filter_basis (with_zero Γ) :=
{ sets := ({({x} : set $ with_zero Γ)} : set (set $ with_zero Γ)),
  ne_empty := by simp,
  directed := by finish }

def with_zero.value : {x : with_zero Γ // ¬ x = 0} → Γ
| ⟨some x, h⟩ := x
| ⟨0, h⟩ := false.rec Γ (ne.irrefl h)


lemma with_zero.value_eq (γ : Γ) : with_zero.value ⟨(γ : with_zero Γ), with_zero.coe_ne_zero⟩ = γ :=
rfl

lemma with_zero.coe_value {x : with_zero Γ} (h : x ≠ 0) : x = coe (with_zero.value ⟨x, h⟩) :=
by with_zero_cases x

variable (Γ)

def with_zero.nhds_basis : nhds_basis (with_zero Γ) :=
{ B := λ x, if h : x = 0 then with_zero.zero_filter_basis Γ
                     else with_zero.coe_filter_basis (with_zero.value (subtype.mk x h)),
  is_nhds := begin
    intro x,
    ext s,
    with_zero_cases x,
    { rw with_zero.nhds_zero_mem,
      simp [with_zero.zero_filter_basis, filter_basis.mem_filter, filter_basis.mem_iff],
      split,
      { rintros ⟨γ₀, h⟩,
        use [{x : with_zero Γ | x < ↑γ₀}, γ₀, h] },
      { rintros ⟨_, ⟨γ₀, rfl⟩, h⟩,
        exact ⟨γ₀, h⟩ } },
    { simpa [with_zero.nhds_coe, filter_basis.mem_filter, filter_basis.mem_iff,
             with_zero.coe_filter_basis] }
  end }

local attribute [instance] with_zero.nhds_basis

lemma with_zero.mem_nhds_basis_zero {U : set $ with_zero Γ} :
  U ∈ nhds_basis.B (0 : with_zero Γ) ↔ ∃ γ : Γ, U = {x : with_zero Γ | x < γ } :=
begin
  dsimp [with_zero.nhds_basis, with_zero.zero_filter_basis],
  simp only [dif_pos],
  convert iff.rfl,
  simp [eq_comm]
end

lemma with_zero.mem_nhds_basis_coe {U : set $ with_zero Γ} {γ₀ : Γ}:
  U ∈ nhds_basis.B (γ₀ : with_zero Γ) ↔ U = {(γ₀ : with_zero Γ)}   :=
begin
  dsimp [with_zero.nhds_basis, with_zero.coe_filter_basis],
  simp only [dif_neg with_zero.coe_ne_zero],
  dsimp [filter_basis.has_mem],
  simpa [with_zero.value]
end

variable {Γ}

-- until the end of this section, all linearly ordered commutative groups will be endowed with
-- the discrete topology
def discrete_ordered_comm_group : topological_space Γ := ⊥

local attribute [instance] discrete_ordered_comm_group
def ordered_comm_group_is_discrete : discrete_topology Γ := ⟨rfl⟩
local attribute [instance] ordered_comm_group_is_discrete

lemma with_zero.comap_coe_nhds (γ : Γ) : nhds γ = comap coe (nhds (γ : with_zero Γ)) :=
begin
  rw [nhds_discrete, filter.comap_pure (λ _ _ h, with_zero.coe_inj.1 h) γ],
  change comap coe (pure (γ : with_zero Γ)) = comap coe (nhds ↑γ),
  rw ← with_zero.nhds_coe γ,
end

lemma with_zero.tendsto_zero {α : Type*} {F : filter α} {f : α → with_zero Γ} :
  tendsto f F (nhds (0 : with_zero Γ)) ↔ ∀ γ₀ : Γ, { x : α | f x < γ₀ } ∈ F :=
begin
  rw nhds_basis.tendsto_into,
  simp only [with_zero.mem_nhds_basis_zero, exists_imp_distrib],
  split ; intro h,
  { intro γ₀,
    exact h {γ | γ < ↑γ₀} γ₀ rfl },
  { rintros _ γ₀ rfl,
    exact h γ₀ }
end

lemma with_zero.mem_nhds_zero {s} :
  s ∈ 𝓝 (0 : with_zero Γ) ↔ ∃ γ : Γ, { x : with_zero Γ | x < γ } ⊆ s :=
begin
  rw nhds_basis.mem_nhds_iff,
  simp only [exists_prop, with_zero.mem_nhds_basis_zero],
  split,
  { rintros ⟨_, ⟨⟨γ, rfl⟩, h⟩⟩,
    exact ⟨γ, h⟩ },
  { rintros ⟨γ, h⟩,
    exact ⟨{x : with_zero Γ | x < γ}, ⟨γ, rfl⟩, h⟩ }
end

lemma with_zero.mem_nhds_coe {s} {γ : Γ} :
  s ∈ 𝓝 (γ : with_zero Γ) ↔ coe γ ∈ s :=
begin
  rw nhds_basis.mem_nhds_iff,
  simp only [exists_prop, with_zero.mem_nhds_basis_coe],
  split,
  { rintros ⟨_, rfl, h⟩,
    rwa singleton_subset_iff at h },
  { intro h,
    use [{coe γ}, rfl],
    rwa singleton_subset_iff },
end

lemma with_zero.tendsto_coe {α : Type*} {F : filter α} {f : α → with_zero Γ} {γ₀ : Γ} :
  tendsto f F (nhds (γ₀ : with_zero Γ)) ↔ { x : α | f x = γ₀ } ∈ F :=
begin
  rw nhds_basis.tendsto_into,
  simp only [with_zero.mem_nhds_basis_coe, forall_eq],
  convert iff.rfl,
  ext s,
  exact mem_singleton_iff.symm
end

lemma with_zero.tendsto_nonzero {α : Type*} {F : filter α} {f : α → with_zero Γ}
  {x₀ : with_zero Γ} (h : x₀ ≠ 0) :
  tendsto f F (nhds (x₀ : with_zero Γ)) ↔ { x : α | f x = x₀ } ∈ F :=
by rw [with_zero.coe_value h, with_zero.tendsto_coe]

instance : topological_monoid (with_zero Γ) :=
⟨begin
  rw continuous_iff_continuous_at,
  rintros ⟨x, y⟩,
  with_zero_cases x y,
  all_goals {
    intros U U_in,
    rw nhds_prod_eq,
    try { simp only [mul_zero, zero_mul] at U_in},
    rw with_zero.mem_nhds_zero at U_in <|> rw [with_zero.mul_coe, with_zero.mem_nhds_coe] at U_in,
    rw mem_map,
    rw mem_prod_same_iff <|> rw mem_prod_iff,
    try { cases U_in with γ hγ  }
    },
  { cases linear_ordered_comm_group.exists_square_le γ with γ₀ hγ₀,
    simp only [with_zero.mem_nhds_zero, exists_prop],
    use [{x : with_zero Γ | x < ↑γ₀}, γ₀, subset.refl _,
         {x : with_zero Γ | x < ↑γ₀}, γ₀, subset.refl _],
    rw set.prod_subset_iff,
    intros x x_in y y_in,
    apply hγ,
    change x*y < γ,
    have := with_zero.mul_lt_mul x_in y_in,
    refine lt_of_lt_of_le this _,
    exact_mod_cast hγ₀ },
  { simp only [set.prod_subset_iff, with_zero.mem_nhds_zero, with_zero.mem_nhds_coe, exists_prop],
    use [{x : with_zero Γ | x < γ*y⁻¹}, γ*y⁻¹, subset.refl _, {y}, mem_singleton _],
    intros x x_in y' y'_in,
    rw mem_singleton_iff at y'_in,
    rw y'_in,
    apply hγ,
    change x * y < γ,
    have := with_zero.mul_lt_right y x_in,
    norm_cast at this,
    rwa [inv_mul_cancel_right] at this },
  { simp only [set.prod_subset_iff, with_zero.mem_nhds_zero, with_zero.mem_nhds_coe, exists_prop],
    use [{x}, mem_singleton _, {y : with_zero Γ | y < γ*x⁻¹}, γ*x⁻¹, subset.refl _],
    intros x' x'_in y y_in,
    rw mem_singleton_iff at x'_in,
    rw x'_in,
    apply hγ,
    change (x : with_zero Γ) * y < γ,
    have := with_zero.mul_lt_right x y_in,
    norm_cast at this,
    rw [inv_mul_cancel_right] at this,
    rwa mul_comm },
  { simp [with_zero.mem_nhds_coe],
    use [{x}, mem_singleton _, {y}, mem_singleton _],
    rw set.prod_subset_iff,
    intros x' x'_in y' y'_in,
    rw mem_singleton_iff at *,
    rw [x'_in, y'_in],
    simpa using U_in },
end⟩
end with_zero_topology
