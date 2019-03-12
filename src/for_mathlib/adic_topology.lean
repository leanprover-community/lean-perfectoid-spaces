/-
This file defines the I-adic topology on a commutative ring R with ideal I.

The ring is wrapped in `adic_ring I := R`, which then receive all relevant type classes.
The end-product is `instance : topological_ring (adic_ring I)`.
-/

import tactic.ring
import data.pnat
import ring_theory.ideal_operations
import topology.algebra.uniform_group topology.algebra.ring

import for_mathlib.topology

open filter set

variables {R : Type*} [comm_ring R]

namespace filter
-- This will be the filter `nhds 0` in our adic-ring
-- The first mathematical key fact is this is indeed a filter
def of_ideal (I : ideal R): filter R :=
{ sets := {s : set R | ∃ n : ℕ, (I^n).carrier ⊆ s},
  univ_sets := ⟨0, by simp⟩,
  sets_of_superset := assume s t ⟨n, hn⟩ st, ⟨n, subset.trans hn st⟩,
  inter_sets := assume s t ⟨n, hn⟩ ⟨m, hm⟩,
    have (I ^ (n + m)).carrier ⊆ (I^n).carrier ∩ (I^m).carrier,
    by rw pow_add ; exact ideal.mul_le_inf,
    ⟨n + m, subset.trans this (inter_subset_inter hn hm)⟩ }

lemma mem_of_ideal_sets {I : ideal R} (s : set R) :
  s ∈ filter.of_ideal I ↔ ∃ n : ℕ, (I^n).carrier ⊆ s := iff.rfl

lemma mem_of_ideal_sets' {I : ideal R} (s : set R) :
  s ∈ filter.of_ideal I ↔ ∃ n > 0, (I^n).carrier ⊆ s :=
begin
  split,
  { rintros ⟨n, H⟩,
    cases n with n H,
    { rw univ_subset_iff.1 H,
      use [1, nat.one_pos],
      simp },
    { use [n+1, nat.add_pos_right n nat.one_pos, H] } },
  { rintros ⟨n, npos, H⟩,
    use [n, H] },
end

-- Next lemma is currently unused, but relates to standard mathlib definition style
lemma of_ideal_eq_infi (I : ideal R) :
  filter.of_ideal I = ⨅ n : ℕ, principal (I^n : ideal R) :=
begin
  apply filter_eq,
  rw infi_sets_eq,
  { ext U,
    simpa [mem_of_ideal_sets] },
  { rintros n m,
    have : (I ^ (n + m)).carrier ⊆ (I^n).carrier ∩ (I^m).carrier,
    by rw pow_add ; exact ideal.mul_le_inf,
    cases (subset_inter_iff.1 this),
    use n+m,
    split ; intros U U_sub ; rw mem_principal_sets at * ;
    exact subset.trans (by assumption) U_sub },
  exact ⟨1⟩
end
end filter

-- Here we check our I-adic neighborhood of zero filter has the required properties to
-- be (nhds 0) in a uniform additive group
def add_group_with_zero_nhd.of_ideal (I : ideal R) : add_group_with_zero_nhd R :=
{ Z := filter.of_ideal I,
  zero_Z := assume U ⟨n, H⟩, mem_pure $ H (I^n).zero_mem,
  sub_Z := begin
             rw tendsto_prod_self_iff,
             rintros U ⟨n, h⟩,
             use [(I^n).carrier, n],
             intros x x' x_in x'_in,
             exact h ((I^n).sub_mem x_in x'_in),
           end,
  ..‹comm_ring R›}

def ideal.adic_topology (I : ideal R) : topological_space R :=
  @add_group_with_zero_nhd.topological_space R (add_group_with_zero_nhd.of_ideal I)

def ideal.adic_ring (I : ideal R) := R

namespace adic_ring
variable {I : ideal R}
open add_group_with_zero_nhd ideal

instance : comm_ring (adic_ring I) := by unfold adic_ring ; apply_instance
instance : topological_space (adic_ring I) := adic_topology I

lemma mem_nhds_zero_iff (I : ideal R) (s : set R) :
  s ∈ nhds (0 : adic_ring I) ↔ ∃ n : ℕ, (I^n).carrier ⊆ s :=
begin
  rw nhds_eq,
  dsimp [adic_ring],
  simp [filter.mem_of_ideal_sets],
  finish,
end

lemma nhds_eq (I : ideal R) {s : set (adic_ring I)} {a : adic_ring I}:
  s ∈ nhds a ↔ ∃ n : ℕ, (λ b, b + a) '' (I^n).carrier ⊆ s :=
begin
  rw [nhds_eq, mem_map, ←nhds_zero_eq_Z, mem_nhds_zero_iff],
  split ;
  { rintros ⟨n, h⟩,
    use n,
    rwa image_subset_iff at * }
end

-- This is the second mathematical key fact: multiplication is continuous in I-adic topology
lemma continuous_mul' : continuous (λ (p : adic_ring I × adic_ring I), p.fst * p.snd) :=
continuous_iff_continuous_at.2 $ assume ⟨x₀, y₀⟩,
begin
  unfold continuous_at,
  rw nhds_prod_eq,
  rw tendsto_prod_iff,
  simp [adic_ring.nhds_eq I] at *,
  rintros V n hV,
  let J := I^n,
  use [(+) x₀ '' J.carrier, n],
  use [(+) y₀ '' J.carrier, n],
  rintros x y ⟨a, a_in, x₀a⟩ ⟨b, b_in, y₀b⟩,
  apply hV,
  have key : (x₀*b + y₀*a + a*b) + x₀*y₀ = x*y, by rw [←x₀a, ←y₀b] ; ring,
  use x₀*b + y₀*a + a*b,
  exact
  ⟨J.add_mem
     (J.add_mem (J.mul_mem_left b_in) (J.mul_mem_left a_in))
     (J.mul_mem_left b_in),
   key⟩,
end

instance : topological_add_group (adic_ring I) :=  by apply add_group_with_zero_nhd.topological_add_group
instance : uniform_space (adic_ring I) := topological_add_group.to_uniform_space _
instance : uniform_add_group (adic_ring I) := topological_add_group_is_uniform
instance : topological_ring (adic_ring I) :=
{ continuous_add := continuous_add',
  continuous_mul := continuous_mul',
  continuous_neg := continuous_neg' }

lemma is_open_pow_ideal (n : ℕ) : @is_open I.adic_ring _ (I^n).carrier :=
begin
  rw [is_open_iff_mem_nhds],
  intros i hi,
  rw nhds_eq,
  use n,
  rintros i' ⟨j, hj, h₂⟩,
  rw ← h₂,
  apply ideal.add_mem _ hj hi,
end

end adic_ring

section

def is_ideal_adic [H : topological_space R] [topological_ring R] (J : ideal R) : Prop :=
H = J.adic_topology

notation `is-`J`-adic` := is_ideal_adic J

lemma is_ideal_adic_iff [topological_space R] [topological_ring R] (J : ideal R) :
  is-J-adic ↔ (∀ n : ℕ, is_open (J^n).carrier) ∧ (∀ s ∈ nhds (0 : R), ∃ n : ℕ, (J^n).carrier ⊆ s) :=
begin
  split,
  { intro H,
    delta is_ideal_adic at H,
    erw H at *,
    split,
    { exact adic_ring.is_open_pow_ideal, },
    { intros s hs,
      erw ← adic_ring.mem_nhds_zero_iff,
      exact hs, }, },
  { rintro ⟨H₁, H₂⟩,
    apply topological_add_group.ext,
    { apply @topological_ring.to_topological_add_group },
    { apply @topological_ring.to_topological_add_group (J.adic_ring) },
    { ext s,
      split; intro H,
      { exact (adic_ring.mem_nhds_zero_iff J s).mpr (H₂ s H) },
      { rcases (adic_ring.mem_nhds_zero_iff J s).mp H with ⟨n, hn⟩,
        rw mem_nhds_sets_iff,
        refine ⟨_, hn, H₁ n, (J^n).zero_mem⟩ } } }
end

variables (R) [topological_space R] [topological_ring R]

def is_adic : Prop := ∃ (J : ideal R), is-J-adic

end
