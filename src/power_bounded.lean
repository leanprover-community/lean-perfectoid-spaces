import for_mathlib.prime
import analysis.topology.topological_space
import analysis.topology.topological_structures
import for_mathlib.topological_structures
import algebra.group_power
import for_mathlib.subring
import tactic.ring


-- This one is by Mario... should go to mathlib
theorem neg_one_pow_eq_or {R} [comm_ring R] : ∀ n : ℕ, ((-1 : R)^n = 1) ∨ ((-1 : R)^n = -1)
| 0     := by simp
| (n+1) := by cases neg_one_pow_eq_or n; simp [pow_succ, h]

variables {R : Type} [comm_ring R] [topological_space R] [topological_ring R]  

/-- Wedhorn Definition 5.27 page 36 -/
definition is_bounded (B : set R) : Prop :=
∀ U ∈ (nhds (0 : R)).sets, ∃ V ∈ (nhds (0 : R)).sets, ∀ v ∈ V, ∀ b ∈ B, v*b ∈ U

definition is_power_bounded (r : R) : Prop := is_bounded (powers r)

variable (R)
definition power_bounded_subring := {r : R | is_power_bounded r}

namespace power_bounded_subring

instance : has_coe (power_bounded_subring R) R := ⟨subtype.val⟩

lemma zero_mem : (0 : R) ∈ power_bounded_subring R :=
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
end

lemma one_mem : (1 : R) ∈ power_bounded_subring R :=
begin
  simp [power_bounded_subring,is_power_bounded,is_bounded,powers],
  intros U hU,
  existsi U,
  split,
  exact hU,
  intros v hv b n hb,
  simpa [hb.symm],
end

lemma neg_mem : ∀ {a : R}, a ∈ power_bounded_subring R → -a ∈ power_bounded_subring R :=
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

lemma mul_mem :
∀ {a b : R}, a ∈ power_bounded_subring R → b ∈ power_bounded_subring R → a * b ∈ power_bounded_subring R :=
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
end

instance : is_subring (power_bounded_subring R) :=
{ zero_mem := power_bounded_subring.zero_mem R,
  one_mem := power_bounded_subring.one_mem R,
  add_mem := sorry,
  neg_mem := λ a, power_bounded_subring.neg_mem R,
  mul_mem := λ a b, power_bounded_subring.mul_mem R }

instance : ring (power_bounded_subring R) := by apply_instance
instance power_bounded_subring_is_comm_ring : comm_ring (power_bounded_subring R) :=
{ mul_comm := assume ⟨a, _⟩ ⟨b, _⟩, subtype.eq $ mul_comm _ _,
  .. power_bounded_subring.ring R }

definition is_uniform : Prop := is_bounded (power_bounded_subring R)

end power_bounded_subring

theorem p_is_power_bounded [p : nat.Prime] : is_power_bounded (p : power_bounded_subring R) := sorry
