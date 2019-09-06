import topology.algebra.ordered

import for_mathlib.filter
import for_mathlib.topology

import valuation.linear_ordered_comm_group_with_zero

local attribute [instance, priority 0] classical.decidable_linear_order
local notation `𝓝` x: 70 := nhds x
variables {Γ : Type*} [linear_ordered_comm_group_with_zero Γ]

namespace linear_ordered_comm_group_with_zero
open topological_space filter set linear_ordered_structure

variables (Γ)
def nhds_fun : Γ → filter Γ :=
  (λ x : Γ, if x = 0 then ⨅ (γ₀ : units Γ), principal {γ | γ < γ₀} else pure x)

protected def topological_space : topological_space Γ :=
topological_space.mk_of_nhds (nhds_fun Γ)

local attribute [instance] linear_ordered_comm_group_with_zero.topological_space

lemma directed_lt : directed (≥) (λ (γ₀ : units Γ), principal {γ : Γ | γ < ↑γ₀}) :=
begin
  intros γ₁ γ₂,
  use min γ₁ γ₂,
  split,
  { change  principal {γ : Γ | γ < ↑(min γ₁ γ₂)} ≤ principal {γ : Γ | γ < ↑γ₁},
    rw [principal_mono, coe_min],
    intros x x_in,
    calc x < min ↑γ₁ ↑γ₂ : x_in
        ... ≤ γ₁ : min_le_left _ _ },
  { change  principal {γ : Γ | γ < ↑(min γ₁ γ₂)} ≤ principal {γ : Γ | γ < ↑γ₂},
    rw [principal_mono, coe_min],
    intros x x_in,
    calc x < min ↑γ₁ ↑γ₂ : x_in
        ... ≤ γ₂ : min_le_right _ _ }
end

lemma pure_le_nhds_fun : pure ≤ nhds_fun Γ :=
begin
  intro x,
  by_cases hx : x = 0; simp [hx, nhds_fun],
end

lemma nhds_fun_ok : ∀ (x : Γ) (s ∈ nhds_fun Γ x),
  (∃ t ∈ nhds_fun Γ x, t ⊆ s ∧ ∀ y ∈ t, s ∈ nhds_fun Γ y) :=
begin
  intros x U U_in,
  by_cases hx : x = 0,
  { simp [hx, nhds_fun] at U_in ⊢,
    rw [mem_infi (directed_lt Γ) ⟨1⟩, mem_Union] at U_in,
    cases U_in with γ₀ h,
    use {γ : Γ | γ < ↑γ₀},
    rw mem_principal_sets at h,
    split,
    { apply mem_infi_sets γ₀,
      rw mem_principal_sets},
    { refine ⟨h, _⟩,
      intros y y_in,
      by_cases hy : y = 0 ; simp [hy],
      { apply mem_infi_sets γ₀,
        rwa mem_principal_sets },
      { exact h y_in } } },
  { simp [hx, nhds_fun] at U_in ⊢,
    use {x},
    refine ⟨mem_singleton _, singleton_subset_iff.2 U_in, _⟩,
    intros y y_in,
    rw mem_singleton_iff at y_in,
    rw y_in,
    simpa [hx] }
end

variables  {Γ}
lemma nhds_coe (γ : units Γ) : nhds (γ : Γ) = pure (γ : Γ) :=
calc nhds (γ : Γ) = nhds_fun Γ γ : nhds_mk_of_nhds (nhds_fun Γ) γ (pure_le_nhds_fun Γ) (nhds_fun_ok Γ)
              ... = pure (γ : Γ) : if_neg (group_with_zero.unit_ne_zero γ)

@[simp] lemma nhds_of_ne_zero (γ : Γ) (h : γ ≠ 0) :
  nhds γ = pure γ :=
nhds_coe (group_with_zero.mk₀ _ h)

lemma singleton_nhds (γ : units Γ) : ({γ} : set Γ) ∈ nhds (γ : Γ) :=
by simp [nhds_coe γ]

lemma nhds_zero_mem (U : set Γ) : U ∈ nhds (0 : Γ) ↔ ∃ γ₀ : units Γ, {x : Γ | x < γ₀} ⊆ U :=
begin
  rw nhds_mk_of_nhds (nhds_fun Γ) 0 (pure_le_nhds_fun Γ) (nhds_fun_ok Γ),
  simp [nhds_fun],
  rw mem_infi (directed_lt Γ) ⟨1⟩,
  { split,
    { rintro ⟨_, ⟨γ₀, rfl⟩, H⟩,
      rw mem_principal_sets at H,
      use [γ₀, H] },
    { rintro ⟨γ₀, H⟩,
      rw mem_Union,
      use γ₀,
      rwa mem_principal_sets } }
end

lemma nhds_zero (γ : units Γ) : {x : Γ | x < γ} ∈ nhds (0 : Γ) :=
by { rw nhds_zero_mem, use γ }

variable (Γ)

def ordered_topology : ordered_topology Γ :=
{ is_closed_le' :=
  begin
    show is_open {p : Γ × Γ | ¬p.fst ≤ p.snd},
    simp only [not_le],
    rw is_open_iff_mem_nhds,
    rintros ⟨a,b⟩ hab,
    change b < a at hab,
    let γ := group_with_zero.mk₀ _ (ne_zero_of_gt hab),
    rw [nhds_prod_eq, mem_prod_iff],
    by_cases hb : b = 0,
    { subst b,
      use [{γ}, singleton_nhds γ, {x : Γ | x < γ}, nhds_zero γ],
      intros p p_in,
      cases mem_prod.1 p_in with h1 h2,
      rw mem_singleton_iff at h1,
      change p.2 < p.1,
      rwa h1 },
    { let b' := group_with_zero.mk₀ _ hb,
      use [{γ}, singleton_nhds γ, {b'}, singleton_nhds b'],
      intros p p_in,
      cases mem_prod.1 p_in with h1 h2,
      rw mem_singleton_iff at h1 h2,
      change p.2 < p.1,
      rwa [h1, h2] }
  end }

local attribute [instance] ordered_topology

lemma t2_space : t2_space Γ := ordered_topology.to_t2_space
local attribute [instance] t2_space

lemma regular_space : regular_space Γ :=
begin
  haveI : t1_space Γ := t2_space.t1_space,
  split,
  intros s x s_closed x_not_in_s,
  by_cases hx : x = 0,
  { refine ⟨s, _, subset.refl _, _⟩,
    { subst x,
      rw is_open_iff_mem_nhds,
      intros y hy,
      by_cases hy' : y = 0, { subst y, contradiction },
      simpa [hy'] },
    { rw inf_eq_bot_iff,
      use -s,
      simp only [exists_prop, mem_principal_sets],
      split,
      exact mem_nhds_sets (by rwa is_open_compl_iff) (by rwa mem_compl_iff),
      exact ⟨s, subset.refl s, by simp⟩ } },
  { let x' := group_with_zero.mk₀ _ hx,
    simp only [inf_eq_bot_iff, exists_prop, mem_principal_sets],
    exact ⟨-{x'}, is_open_compl_iff.mpr is_closed_singleton, by rwa subset_compl_singleton_iff,
          {x'}, singleton_nhds x', -{x'}, by simp [subset.refl]⟩ }
end

def zero_filter_basis : filter_basis Γ :=
{ sets := range (λ γ : units Γ, {x : Γ | x < γ}),
  ne_empty := range_ne_empty.mpr ⟨1⟩,
  directed := begin
    intros s t hs ht,
    rw mem_range at hs ht,
    rcases hs with ⟨γs, rfl⟩,
    rcases ht with ⟨γt, rfl⟩,
    simp only [exists_prop, mem_range],
    rcases directed_lt Γ γs γt with ⟨γ, hs, ht⟩,
    change principal {g : Γ | g < ↑γ} ≤ principal {g : Γ | g < ↑γt} at ht,
    change principal {g : Γ | g < ↑γ} ≤ principal {g : Γ | g < ↑γs} at hs,
    rw [le_principal_iff, mem_principal_sets] at hs ht,
    use [{x : Γ | x < γ}, γ, rfl, subset_inter_iff.mpr ⟨hs, ht⟩]
  end}

variable {Γ}

def coe_filter_basis (x : Γ) (h : x ≠ 0) : filter_basis Γ :=
{ sets := ({({x} : set Γ)} : set (set Γ)),
  ne_empty := by simp,
  directed := by finish }

variable (Γ)

def nhds_basis : nhds_basis Γ :=
{ B := λ x, if h : x = 0 then zero_filter_basis Γ
                     else coe_filter_basis x h,
  is_nhds := begin
    intro x,
    ext s,
    split_ifs with hx,
    { subst x,
      rw nhds_zero_mem,
      simp [zero_filter_basis, filter_basis.mem_filter, filter_basis.mem_iff],
      split,
      { rintros ⟨γ₀, h⟩,
        use [{x : Γ | x < ↑γ₀}, γ₀, h] },
      { rintros ⟨_, ⟨γ₀, rfl⟩, h⟩,
        exact ⟨γ₀, h⟩ } },
    { simp [hx, filter_basis.mem_filter, filter_basis.mem_iff, coe_filter_basis], }
  end }

local attribute [instance] nhds_basis

lemma mem_nhds_basis_zero {U : set Γ} :
  U ∈ nhds_basis.B (0 : Γ) ↔ ∃ γ : units Γ, U = {x : Γ | x < γ } :=
begin
  dsimp [nhds_basis, zero_filter_basis],
  simp only [dif_pos],
  convert iff.rfl,
  simp [eq_comm]
end

lemma mem_nhds_basis_nonzero {U : set Γ} {γ₀ : Γ} (h : γ₀ ≠ 0) :
  U ∈ nhds_basis.B γ₀ ↔ U = {γ₀} :=
begin
  dsimp [nhds_basis],
  simp only [dif_neg h],
  dsimp [filter_basis.has_mem, coe_filter_basis γ₀ h],
  exact set.mem_singleton_iff
end

variable {Γ}

-- until the end of this section, all linearly ordered commutative groups will be endowed with
-- the discrete topology
variables (α : Type*) [linear_ordered_comm_group α]
def discrete_ordered_comm_group : topological_space α := ⊥

local attribute [instance] discrete_ordered_comm_group
def ordered_comm_group_is_discrete : discrete_topology α := ⟨rfl⟩
local attribute [instance] ordered_comm_group_is_discrete

lemma comap_coe_nhds (γ : units Γ) : nhds γ = comap coe (nhds (γ : Γ)) :=
begin
  rw [nhds_discrete, filter.comap_pure (λ _ _ h, units.ext h) γ],
  change comap coe (pure (γ : Γ)) = comap coe (nhds ↑γ),
  rw ← nhds_coe γ,
end

lemma tendsto_zero {α : Type*} {F : filter α} {f : α → Γ} :
  tendsto f F (nhds (0 : Γ)) ↔ ∀ γ₀ : units Γ, { x : α | f x < γ₀ } ∈ F :=
begin
  rw nhds_basis.tendsto_into,
  simp only [mem_nhds_basis_zero, exists_imp_distrib],
  split ; intro h,
  { intro γ₀,
    exact h {γ | γ < ↑γ₀} γ₀ rfl },
  { rintros _ γ₀ rfl,
    exact h γ₀ }
end

lemma mem_nhds_zero {s} :
  s ∈ 𝓝 (0 : Γ) ↔ ∃ γ : units Γ, { x : Γ | x < γ } ⊆ s :=
begin
  rw nhds_basis.mem_nhds_iff,
  simp only [exists_prop, mem_nhds_basis_zero],
  split,
  { rintros ⟨_, ⟨⟨γ, rfl⟩, h⟩⟩,
    exact ⟨γ, h⟩ },
  { rintros ⟨γ, h⟩,
    exact ⟨{x : Γ | x < γ}, ⟨γ, rfl⟩, h⟩ }
end

lemma mem_nhds_coe {s} {γ : Γ} (h : γ ≠ 0) :
  s ∈ 𝓝 γ ↔ γ ∈ s :=
begin
  rw nhds_basis.mem_nhds_iff,
  simp only [exists_prop, mem_nhds_basis_nonzero _ h, h],
  split,
  { rintros ⟨_, rfl, h₂⟩,
    rwa singleton_subset_iff at h₂ },
  { intro h,
    use [{γ}, rfl],
    rwa singleton_subset_iff },
end

lemma tendsto_nonzero {α : Type*} {F : filter α} {f : α → Γ} {γ₀ : Γ} (h : γ₀ ≠ 0) :
  tendsto f F (nhds (γ₀ : Γ)) ↔ { x : α | f x = γ₀ } ∈ F :=
begin
  rw nhds_basis.tendsto_into,
  simp only [mem_nhds_basis_nonzero _ h, forall_eq],
  convert iff.rfl,
  ext s,
  exact mem_singleton_iff.symm
end

instance : topological_monoid Γ :=
⟨begin
  rw continuous_iff_continuous_at,
  rintros ⟨x, y⟩,
  by_cases hx : x = 0; by_cases hy : y = 0,
  all_goals {
    try {subst x}, try {subst y},
    intros U U_in,
    rw nhds_prod_eq,
    try { simp only [_root_.mul_zero, _root_.zero_mul] at U_in},
    rw mem_nhds_zero at U_in <|> rw [mem_nhds_coe] at U_in,
    rw mem_map,
    rw mem_prod_same_iff <|> rw mem_prod_iff,
    try { cases U_in with γ hγ } },
  { cases linear_ordered_structure.exists_square_le γ with γ₀ hγ₀,
    simp only [mem_nhds_zero, exists_prop],
    use [{x : Γ | x < ↑γ₀}, γ₀, subset.refl _, {x : Γ | x < ↑γ₀}, γ₀, subset.refl _],
    rw set.prod_subset_iff,
    intros x x_in y y_in,
    apply hγ,
    change x*y < γ,
    have := mul_lt_mul' x_in y_in,
    refine lt_of_lt_of_le this _,
    exact_mod_cast hγ₀ },
  { simp only [set.prod_subset_iff, mem_nhds_zero, mem_nhds_coe hy, exists_prop],
    use [{x : Γ | x < γ*y⁻¹}, γ * (group_with_zero.mk₀ y hy)⁻¹, subset.refl _,
      {(group_with_zero.mk₀ y hy)}, mem_singleton y],
    intros x x_in y' y'_in,
    rw mem_singleton_iff at y'_in,
    rw y'_in,
    apply hγ,
    change x * y < γ,
    simpa [hy] using mul_lt_right' y x_in hy, },
  { simp only [set.prod_subset_iff, mem_nhds_zero, mem_nhds_coe hx, exists_prop],
    use [{(group_with_zero.mk₀ x hx)}, mem_singleton _, {y : Γ | y < γ*x⁻¹},
      γ * (group_with_zero.mk₀ x hx)⁻¹, subset.refl _],
    intros x' x'_in y y_in,
    rw mem_singleton_iff at x'_in,
    rw x'_in,
    apply hγ,
    change x * y < γ,
    rw mul_comm,
    simpa [hx] using mul_lt_right' x y_in hx, },
  { simp [mem_nhds_coe, hx, hy],
    use [{x}, mem_singleton _, {y}, mem_singleton _],
    rw set.prod_subset_iff,
    intros x' x'_in y' y'_in,
    rw mem_singleton_iff at *,
    rw [x'_in, y'_in],
    simpa using U_in },
  { assume H, simp at H, tauto }
end⟩

end linear_ordered_comm_group_with_zero
