import topology.basic
import topology.algebra.ring
import algebra.group_power
import ring_theory.subring
import tactic.ring

import nonarchimedean_ring

/- The theory of topologically nilpotent, bounded, and power-bounded
   elements and subsets of topological rings.

-/

variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]

/-- Wedhorn Definition 5.25 page 36 -/
definition is_topologically_nilpotent (r : R) : Prop :=
∀ U ∈ (nhds (0 : R)), ∃ N : ℕ, ∀ n : ℕ, n > N → r^n ∈ U

def monoid.set_pow {R : Type*} [monoid R] (T : set R) : ℕ → set R
| 0 := {1}
| (n + 1) := ((*) <$> monoid.set_pow n <*> T)

def is_topologically_nilpotent_subset (T : set R) : Prop :=
∀ U ∈ (nhds (0 : R)), ∃ n : ℕ, monoid.set_pow T n ⊆ U

namespace topologically_nilpotent

-- don't know what to prove

end topologically_nilpotent

/-- Wedhorn Definition 5.27 page 36 -/
definition is_bounded (B : set R) : Prop :=
∀ U ∈ (nhds (0 : R)), ∃ V ∈ (nhds (0 : R)), ∀ v ∈ V, ∀ b ∈ B, v*b ∈ U

namespace bounded

-- TODO : PR to mathlib (branch kmb-top-monoid; compiling)
lemma is_add_submonoid.mem_nhds_zero {G : Type*} [topological_space G] [add_monoid G]
  [topological_add_monoid G] (H : set G) [is_add_submonoid H] (hH : is_open H) :
  H ∈ nhds (0 : G) :=
begin
  rw mem_nhds_sets_iff,
  use H,
  use (by refl),
  split, use hH,
  exact is_add_submonoid.zero_mem _,
end

set_option trace.simplify.rewrite true

lemma span_bounded_of_bounded (hR : nonarchimedean R) (T : set R)
  (hT : is_bounded T) : is_bounded (add_group.closure T) :=
begin
  intros U hU,
  -- find subgroup U' in U
  rcases hR U hU with ⟨U', hU', hoU', hsU'⟩,
  -- U' still a nhd
  resetI,
  have hnU' : U' ∈ nhds (0 : R) := is_add_submonoid.mem_nhds_zero U' hoU',
  -- Use boundedness hypo for T with U' to get V
  rcases hT U' hnU' with ⟨V, hV, hB⟩,
  -- find subgroup V' in V
  rcases hR V hV with ⟨V', hV', hoV', hsV'⟩,
  -- it's still a nhd
  haveI := hV',
--  resetI,
  have hnV' : V' ∈ nhds (0 : R) := is_add_submonoid.mem_nhds_zero V' hoV',
  -- V' works for our proof
  use V', use hnV',
  intros v hv b hb,
  -- Suffices to prove we're in U'
  apply hsU',
  -- Prove the result by induction
  apply add_group.in_closure.rec_on hb,
  { intros t ht,
    exact hB v (hsV' hv) t ht,
  },
  { rw mul_zero, exact mem_of_nhds hnU'},
  { intros a Ha Hv,
    rwa [←neg_mul_comm, neg_mul_eq_neg_mul_symm, is_add_subgroup.neg_mem_iff],
  },
  { intros a b ha hb Ha Hb,
    rw [mul_add],
    exact is_add_submonoid.add_mem Ha Hb,
  }
end

end bounded

definition is_power_bounded (r : R) : Prop := is_bounded (powers r)

definition is_power_bounded_subset {T : set R} : Prop := is_bounded (monoid.closure T)

namespace power_bounded

protected lemma zero : is_power_bounded (0 : R) :=
λ U hU, ⟨U,
begin
  split, {exact hU},
  intros v hv b H,
  cases H with n H,
  induction n ; { simp [H.symm, pow_succ, mem_of_nhds hU], try {assumption} }
end⟩

protected lemma one : is_power_bounded (1 : R) :=
λ U hU, ⟨U,
begin
  split, {exact hU},
  intros v hv b H,
  cases H with n H,
  simpa [H.symm]
end⟩

-- need mul for add
protected lemma mul (a b : R)
  (ha : is_power_bounded a) (hb : is_power_bounded b) :
  is_power_bounded (a * b) :=
λ U U_nhd,
begin
  rcases hb U U_nhd with ⟨Vb, Vb_nhd, hVb⟩,
  rcases ha Vb Vb_nhd with ⟨Va, Va_nhd, hVa⟩,
  clear ha hb,
  use Va,
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

protected lemma add (hR : nonarchimedean R) (a b : R)
  (ha : is_power_bounded a) (hb : is_power_bounded b) :
  is_power_bounded (a + b) :=
λ U U_nhd,
begin
  sorry
end


end power_bounded

variable (R)
-- definition makes sense for all R, but it's only a subring for certain
-- rings e.g. non-archimedean rings.
definition power_bounded_subring := {r : R | is_power_bounded r}

namespace power_bounded

instance : has_coe (power_bounded_subring R) R := ⟨subtype.val⟩

lemma zero_mem : (0 : R) ∈ power_bounded_subring R := power_bounded.zero

lemma one_mem : (1 : R) ∈ power_bounded_subring R := power_bounded.one

lemma mul_mem :
∀ {a b : R}, a ∈ power_bounded_subring R → b ∈ power_bounded_subring R → a * b ∈ power_bounded_subring R :=
power_bounded.mul

lemma neg_mem : ∀ {a : R}, a ∈ power_bounded_subring R → -a ∈ power_bounded_subring R :=
λ a ha U hU,
begin
  let Usymm := U ∩ {u | -u ∈ U},
  let hUsymm : Usymm ∈ (nhds (0 : R)) :=
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

instance submonoid : is_submonoid (power_bounded_subring R) :=
{ one_mem := power_bounded.one_mem R,
  mul_mem := λ a b, power_bounded.mul_mem R }

definition is_uniform : Prop := is_bounded (power_bounded_subring R)

end power_bounded
