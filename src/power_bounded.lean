import for_mathlib.prime
import analysis.topology.topological_space
import analysis.topology.topological_structures
import for_mathlib.topological_structures
import algebra.group_power
import for_mathlib.subring
import tactic.ring

section topological_ring
variables {R : Type} [comm_ring R] [topological_space R] [topological_ring R]  

/-- Wedhorn Definition 5.27 page 36 -/
definition is_bounded (B : set R) : Prop :=
∀ U ∈ (nhds (0 : R)).sets, ∃ V ∈ (nhds (0 : R)).sets, ∀ v ∈ V, ∀ b ∈ B, v*b ∈ U

definition is_power_bounded (r : R) : Prop := is_bounded (powers r)

variable (R)
definition power_bounded_subring := {r : R | is_power_bounded r}

instance power_bounded_subring_to_ring : has_coe (power_bounded_subring R) R := ⟨subtype.val⟩
instance : is_submonoid (power_bounded_subring R) :=
{ one_mem :=
  begin
    simp [power_bounded_subring,is_power_bounded,is_bounded,powers],
    intros U hU,
    existsi U,
    split,
    exact hU,
    intros v hv b n hb,
    simpa [hb.symm],
  end,
  mul_mem :=
  begin
    simp [power_bounded_subring,is_power_bounded,is_bounded,powers],
    intros a b ha hb U hU,
    replace ha := ha U hU,
    replace hb := hb U hU,
    cases ha with Va hVa,
    cases hb with Vb hVb,
    existsi Va ∩ Vb, -- just my wild guess. Is it even math-true?
    split,
    apply filter.inter_mem_sets hVa.1 hVb.1,
    { intros v hv x n hx,
      sorry } 
  end }

-- This one is by Mario... should go to mathlib
theorem neg_one_pow_eq_or {R} [comm_ring R] : ∀ n : ℕ, ((-1 : R)^n = 1) ∨ ((-1 : R)^n = -1)
| 0     := by simp
| (n+1) := by cases neg_one_pow_eq_or n; simp [pow_succ, h]

instance : is_add_subgroup (power_bounded_subring R) :=
{ zero_mem :=
  begin
    simp [power_bounded_subring,is_power_bounded,is_bounded,powers],
    intros U hU,
    existsi U,
    split,
    exact hU,
    intros v hv b n,
    induction n,
    { simp,
      intro hb,
      rw ← hb,
      simpa },
    { intro hb,
      rw ← hb,
      simp [pow_succ],
      exact mem_of_nhds hU }
  end,
  add_mem := sorry,
  neg_mem :=
  begin
    simp [power_bounded_subring,is_power_bounded,is_bounded,powers],
    intros a ha U hU,
    let Usymm := U ∩ {u | -u ∈ U},
    let hUsymm : Usymm ∈ (nhds (0 : R)).sets :=
    begin
      apply filter.inter_mem_sets hU,
      apply continuous.tendsto (topological_add_group.continuous_neg R) 0,
      simpa
    end,
    replace ha := ha Usymm hUsymm,
    cases ha with V hV,
    existsi V,
    split,
    exact hV.1,
    replace hV := hV.2,
    intros v hv b n hb,
    rw ← hb,
    rw show v * (-a)^n = ((-1)^n * v) * a^n,
    begin
      rw [neg_eq_neg_one_mul, mul_pow], ring,
    end,
    have H := hV v hv (a^n) n rfl,
    suffices : (-1)^n * v * a^n ∈ Usymm,
    { exact this.1 },
    { simp,
      cases (@neg_one_pow_eq_or R _ n) with h h;
      { dsimp [Usymm] at H,
        simp [h, H.1, H.2] } }
  end
}

instance : is_subring (power_bounded_subring R) :=
{ .. power_bounded_subring.is_add_subgroup R,
  .. power_bounded_subring.is_submonoid R }
instance power_bounded_subring_is_ring : ring (power_bounded_subring R) := by apply_instance
instance power_bounded_subring_is_comm_ring : comm_ring (power_bounded_subring R) :=
{ mul_comm := assume ⟨a, _⟩ ⟨b, _⟩, subtype.eq $ mul_comm _ _,
  .. power_bounded_subring_is_ring R }
instance : topological_space (power_bounded_subring R) := by apply subtype.topological_space
instance : topological_ring (power_bounded_subring R) := -- this should be done in general in subring, I think.
{ continuous_add := sorry,
  continuous_mul := sorry,
  continuous_neg := sorry,
  .. power_bounded_subring_is_comm_ring R,
  .. power_bounded_subring.topological_space R }

definition is_uniform : Prop := is_bounded (power_bounded_subring R)

theorem p_is_power_bounded [p : nat.Prime] : is_power_bounded (p : power_bounded_subring R) := sorry

end topological_ring