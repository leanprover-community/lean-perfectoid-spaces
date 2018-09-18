import analysis.topology.topological_space
import analysis.topology.topological_structures
import for_mathlib.topological_structures
import algebra.group_power
import ring_theory.subring

universe u

variables {R : Type u} [comm_ring R] [topological_space R] [topological_ring R]

/-- Wedhorn Definition 5.27 page 36 -/
definition is_bounded (B : set R) : Prop :=
∀ U ∈ (nhds (0 : R)).sets, ∃ V ∈ (nhds (0 : R)).sets, ∀ v ∈ V, ∀ b ∈ B, v*b ∈ U

definition is_power_bounded (r : R) : Prop := is_bounded (powers r)

variable (R)
definition power_bounded_subring := {r : R | is_power_bounded r}

namespace power_bounded

instance : is_subring (power_bounded_subring R) := sorry
instance : has_coe (power_bounded_subring R) R := ⟨subtype.val⟩

lemma zero_mem : (0 : R) ∈ power_bounded_subring R :=
λ U hU, ⟨U,
begin
  split, {exact hU},
  intros v hv b H,
  cases H with n H,
  induction n ; { simp [H.symm, pow_succ, mem_of_nhds hU], try {assumption} }
end⟩

lemma one_mem : (1 : R) ∈ power_bounded_subring R :=
λ U hU, ⟨U,
begin
  split, {exact hU},
  intros v hv b H,
  cases H with n H,
  simpa [H.symm]
end⟩

lemma mul_mem :
∀ {a b : R}, a ∈ power_bounded_subring R → b ∈ power_bounded_subring R → a * b ∈ power_bounded_subring R :=
λ a b ha hb U U_nhd,
begin
  rcases hb U U_nhd with ⟨Vb, ⟨Vb_nhd, hVb⟩⟩,
  rcases ha Vb Vb_nhd with ⟨Va, ⟨Va_nhd, hVa⟩⟩,
  clear ha hb,
  existsi Va,
  split, {exact Va_nhd},
  { intros v hv x H,
    cases H with n hx,
    rw [← hx,
          mul_pow,
        ← mul_assoc],
    apply hVb (v * a^n) _ _ _,
    apply hVa v hv _ _,
    repeat { dsimp [powers],
      existsi n,
      refl } }
end

lemma neg_mem : ∀ {a : R}, a ∈ power_bounded_subring R → -a ∈ power_bounded_subring R :=
λ a ha U hU,
begin
  let Usymm := U ∩ {u | -u ∈ U},
  let hUsymm : Usymm ∈ (nhds (0 : R)).sets :=
  begin
    apply filter.inter_mem_sets hU,
    apply continuous.tendsto (topological_add_group.continuous_neg R) 0,
    simpa
  end,
  rcases ha Usymm hUsymm with ⟨V, ⟨V_nhd, hV⟩⟩,
  clear hUsymm,
  existsi V,
  split, {exact V_nhd},
  intros v hv b H,
  cases H with n hb,
  rw ← hb,
  rw show v * (-a)^n = ((-1)^n * v) * a^n,
  begin
    rw [neg_eq_neg_one_mul, mul_pow], ring,
  end,
  have H := hV v hv (a^n) _,
  suffices : (-1)^n * v * a^n ∈ Usymm,
  { exact this.1 },
  { simp,
    cases (@neg_one_pow_eq_or R _ n) with h h;
    { dsimp [Usymm] at H,
      simp [h, H.1, H.2] } },
  { dsimp [powers],
      existsi n,
      refl }
end

instance : is_submonoid (power_bounded_subring R) :=
{ one_mem := power_bounded.one_mem R,
mul_mem := λ a b, power_bounded.mul_mem R }

definition is_uniform : Prop := is_bounded (power_bounded_subring R)

end power_bounded
