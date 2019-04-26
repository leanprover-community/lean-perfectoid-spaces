import topology.basic
import topology.algebra.ring
import algebra.group_power
import ring_theory.subring
import tactic.ring

import for_mathlib.submonoid
import for_mathlib.topological_rings
import for_mathlib.nonarchimedean.adic_topology

local attribute [instance] set.pointwise_mul_semiring

/- The theory of topologically nilpotent, bounded, and power-bounded
   elements and subsets of topological rings.

-/

variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]

/-- Wedhorn Definition 5.25 page 36 -/
definition is_topologically_nilpotent (r : R) : Prop :=
∀ U ∈ (nhds (0 : R)), ∃ N : ℕ, ∀ n : ℕ, n > N → r^n ∈ U

-- def monoid.set_pow {R : Type*} [monoid R] (T : set R) : ℕ → set R
-- | 0 := {1}
-- | (n + 1) := ((*) <$> monoid.set_pow n <*> T)

def is_topologically_nilpotent_subset (T : set R) : Prop :=
∀ U ∈ (nhds (0 : R)), ∃ n : ℕ, T ^ n ⊆ U

namespace topologically_nilpotent

-- don't know what to prove

end topologically_nilpotent

/-- Wedhorn Definition 5.27 page 36 -/
definition is_bounded (B : set R) : Prop :=
∀ U ∈ nhds (0 : R), ∃ V ∈ nhds (0 : R), ∀ v ∈ V, ∀ b ∈ B, v*b ∈ U

lemma is_bounded_iff (B : set R) :
  is_bounded B ↔ ∀ U ∈ nhds (0 : R), ∃ V ∈ nhds (0 : R), V * B ⊆ U :=
forall_congr $ λ U, imp_congr iff.rfl $ exists_congr $ λ V, exists_congr $ λ hV,
begin
  split,
  { rintros H _ ⟨v, hv, b, hb, rfl⟩, exact H v hv b hb },
  { intros H v hv b hb, exact H ⟨v, hv, b, hb, rfl⟩ }
end

section
open submodule topological_add_group

set_option class.instance_max_depth 80

lemma is_bounded_add_subgroup_iff (hR : nonarchimedean R) (B : set R) [is_add_subgroup B] :
  is_bounded B ↔ ∀ U ∈ nhds (0:R), ∃ V : open_add_subgroup R,
    (↑((V : set R) • span ℤ B) : set R) ⊆ U :=
begin
  split,
  { rintros H U hU,
    cases hR U hU with W hW,
    rw is_bounded_iff at H,
    rcases H _ W.mem_nhds_zero with ⟨V', hV', H'⟩,
    cases hR V' hV' with V hV,
    use V,
    refine set.subset.trans _ hW,
    change ↑(span _ _ * span _ _) ⊆ _,
    rw [span_mul_span, ← add_group_closure_eq_spanℤ, add_group.closure_subset_iff],
    exact set.subset.trans (set.mul_le_mul hV (set.subset.refl B)) H' },
  { intros H,
    rw is_bounded_iff,
    intros U hU,
    cases H U hU with V hV,
    use [V, V.mem_nhds_zero],
    refine set.subset.trans _ hV,
    rintros _ ⟨v, hv, b, hb, rfl⟩,
    exact mul_mem_mul (subset_span hv) (subset_span hb) }
end

lemma is_ideal_adic.topologically_nilpotent {J : ideal R} (h : is-J-adic) :
  is_topologically_nilpotent_subset (↑J : set R) :=
begin
  rw is_ideal_adic_iff at h,
  intros U hU,
  cases h.2 U hU with n hn,
  use n,
  exact set.subset.trans (J.pow_subset_pow) hn
end

end

namespace bounded
open topological_add_group

lemma subset {B C : set R} (h : B ⊆ C) (hC : is_bounded C) : is_bounded B :=
λ U hU, exists.elim (hC U hU) $ λ V ⟨hV, hC⟩, ⟨V, hV, λ v hv b hb, hC v hv b $ h hb⟩

-- TODO : this is PR 809 to mathlib, remove when it hits
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

lemma add_group.closure (hR : nonarchimedean R) (T : set R)
  (hT : is_bounded T) : is_bounded (add_group.closure T) :=
begin
  intros U hU,
  -- find subgroup U' in U
  rcases hR U hU with ⟨U', hU'⟩,
  -- U' still a nhd
  -- Use boundedness hypo for T with U' to get V
  rcases hT (U' : set R) U'.mem_nhds_zero with ⟨V, hV, hB⟩,
  -- find subgroup V' in V
  rcases hR V hV with ⟨V', hV'⟩,
  -- V' works for our proof
  use [V', V'.mem_nhds_zero],
  intros v hv b hb,
  -- Suffices to prove we're in U'
  apply hU',
  -- Prove the result by induction
  apply add_group.in_closure.rec_on hb,
  { intros t ht,
    exact hB v (hV' hv) t ht },
  { rw mul_zero, exact U'.zero_mem },
  { intros a Ha Hv,
    rwa [←neg_mul_comm, neg_mul_eq_neg_mul_symm, is_add_subgroup.neg_mem_iff] },
  { intros a b ha hb Ha Hb,
    rw [mul_add],
    exact U'.add_mem Ha Hb }
end

end bounded

definition is_power_bounded (r : R) : Prop := is_bounded (powers r)

definition is_power_bounded_subset (T : set R) : Prop := is_bounded (monoid.closure T)

namespace power_bounded
open topological_add_group

lemma zero : is_power_bounded (0 : R) :=
λ U hU, ⟨U,
begin
  split, {exact hU},
  intros v hv b H,
  induction H with n H,
  induction n ; { simp [H.symm, pow_succ, mem_of_nhds hU], try {assumption} }
end⟩

lemma one : is_power_bounded (1 : R) :=
λ U hU, ⟨U,
begin
  split, {exact hU},
  intros v hv b H,
  cases H with n H,
  simpa [H.symm]
end⟩

lemma singleton (r : R) : is_power_bounded r ↔ is_power_bounded_subset ({r} : set R) :=
begin
  unfold is_power_bounded,
  unfold is_power_bounded_subset,
  rw monoid.closure_singleton,
end

lemma subset {B C : set R} (h : B ⊆ C) (hC : is_power_bounded_subset C) :
  is_power_bounded_subset B :=
λ U hU, exists.elim (hC U hU) $
  λ V ⟨hV, hC⟩, ⟨V, hV, λ v hv b hb, hC v hv b $ monoid.closure_mono h hb⟩

lemma union {S T : set R} (hS : is_power_bounded_subset S) (hT : is_power_bounded_subset T) :
  is_power_bounded_subset (S ∪ T) :=
begin
  intros U hU,
  rcases hT U hU with ⟨V, hV, hVU⟩,
  rcases hS V hV with ⟨W, hW, hWV⟩,
  use W, use hW, -- this is wrong
  intros v hv b hb,
  rw monoid.mem_closure_union_iff at hb,
  rcases hb with ⟨y, hy, z, hz, hyz⟩,
  rw [←hyz, ←mul_assoc],
  apply hVU _ _ _ hz,
  exact hWV _ hv _ hy,
end

lemma mul (a b : R)
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

lemma add_group.closure (hR : nonarchimedean R) {T : set R}
  (hT : is_power_bounded_subset T) : is_power_bounded_subset (add_group.closure T) :=
begin
  refine bounded.subset _ (bounded.add_group.closure hR _ hT),
  intros a ha,
  apply monoid.in_closure.rec_on ha,
  { apply add_group.closure_mono,
    exact monoid.subset_closure
  },
  { apply add_group.mem_closure,
    exact monoid.in_closure.one _
  },
  { intros a b ha hb Ha Hb,
    haveI : is_subring (add_group.closure (monoid.closure T)) := ring.is_subring,
    exact is_submonoid.mul_mem Ha Hb,
  }
end

lemma monoid.closure (hR : nonarchimedean R) {T : set R}
  (hT : is_power_bounded_subset T) : is_power_bounded_subset (monoid.closure T) :=
begin
  refine bounded.subset _ hT,
  apply monoid.closure_subset,
  refl,
end

lemma ring.closure (hR : nonarchimedean R) (T : set R)
  (hT : is_power_bounded_subset T) : is_power_bounded_subset (ring.closure T) :=
add_group.closure hR $ monoid.closure hR hT

lemma ring.closure' (hR : nonarchimedean R) (T : set R)
  (hT : is_power_bounded_subset T) : is_bounded (_root_.ring.closure T) :=
bounded.subset monoid.subset_closure (ring.closure hR _ hT)

lemma add (hR : nonarchimedean R) (a b : R)
  (ha : is_power_bounded a) (hb : is_power_bounded b) :
  is_power_bounded (a + b) :=
begin
  rw singleton at ha hb ⊢,
  have hab := add_group.closure hR (union ha hb),
  refine subset _ hab,
  rw set.singleton_subset_iff,
  apply is_add_submonoid.add_mem;
    apply add_group.subset_closure;
    simp
end

end power_bounded

variable (R)
-- definition makes sense for all R, but it's only a subring for certain
-- rings e.g. non-archimedean rings.
definition power_bounded_subring := {r : R | is_power_bounded r}

variable {R}

namespace power_bounded_subring
open topological_add_group

instance : has_coe (power_bounded_subring R) R := ⟨subtype.val⟩

lemma zero_mem : (0 : R) ∈ power_bounded_subring R := power_bounded.zero

lemma one_mem : (1 : R) ∈ power_bounded_subring R := power_bounded.one

lemma add_mem (h : nonarchimedean R) ⦃a b : R⦄ (ha : a ∈ power_bounded_subring R)
  (hb : b ∈ power_bounded_subring R) : a + b ∈ power_bounded_subring R :=
power_bounded.add h a b ha hb

lemma mul_mem :
∀ ⦃a b : R⦄, a ∈ power_bounded_subring R → b ∈ power_bounded_subring R → a * b ∈ power_bounded_subring R :=
power_bounded.mul

lemma neg_mem : ∀ ⦃a : R⦄, a ∈ power_bounded_subring R → -a ∈ power_bounded_subring R :=
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

instance : is_submonoid (power_bounded_subring R) :=
{ one_mem := one_mem,
  mul_mem := mul_mem }

instance (hR : nonarchimedean R) : is_add_subgroup (power_bounded_subring R) :=
{ zero_mem := zero_mem,
  add_mem := add_mem hR,
  neg_mem := neg_mem  }

instance (hR : nonarchimedean R) : is_subring (power_bounded_subring R) :=
{ ..power_bounded_subring.is_submonoid,
  ..power_bounded_subring.is_add_subgroup hR }

variable (R)
definition is_uniform : Prop := is_bounded (power_bounded_subring R)

end power_bounded_subring

section
open set

lemma is_adic.is_bounded (h : is_adic R) : is_bounded (univ : set R) :=
begin
  intros U hU,
  rw mem_nhds_sets_iff at hU,
  rcases hU with ⟨V, hV₁, ⟨hV₂, h0⟩⟩,
  tactic.unfreeze_local_instances,
  rcases h with ⟨J, hJ⟩,
  rw is_ideal_adic_iff at hJ,
  have H : (∃ (n : ℕ), (J^n).carrier ⊆ V) :=
  begin
    apply hJ.2,
    exact mem_nhds_sets hV₂ h0,
  end,
  rcases H with ⟨n, hn⟩,
  use (J^n).carrier, -- the key step
  split,
  { exact mem_nhds_sets (hJ.1 n) (J^n).zero_mem },
  { rintros a ha b hb,
    apply hV₁,
    exact hn ((J^n).mul_mem_right ha), }
end

lemma is_bounded_subset (S₁ S₂ : set R) (h : S₁ ⊆ S₂) (H : is_bounded S₂) : is_bounded S₁ :=
begin
  intros U hU,
  rcases H U hU with ⟨V, hV₁, hV₂⟩,
  use [V, hV₁],
  intros v hv b hb,
  exact hV₂ _ hv _ (h hb),
end

end
