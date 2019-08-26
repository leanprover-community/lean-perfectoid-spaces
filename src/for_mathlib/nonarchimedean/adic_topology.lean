import for_mathlib.nonarchimedean.basic
import for_mathlib.nonarchimedean.is_subgroups_basis

local prefix 𝓝:100 := nhds

variables {R : Type*} [comm_ring R]

namespace ideal
open lattice topological_add_group

-- Note: making the following an instance is useless, instance resolution would never guess I
def adic_basis (I : ideal R) : subgroups_basis R :=
begin
  apply subgroups_basis.of_indexed_submodules_of_comm  (λ n : ℕ, I^n),
  { intros i j,
    use (i + j),
    simp only [],
    rw pow_add,
    exact mul_le_inf },
  { intros r i,
    use i,
    exact le_trans mul_le_inf inf_le_right },
  { intro i,
    use i,
    exact le_trans mul_le_inf inf_le_left }
end

def adic_topology (I : ideal R) : topological_space R :=
begin
  letI := adic_basis I,
  exact (ring_filter_basis.to_add_group_filter_basis R).topology,
end

def is_ideal_adic [H : topological_space R] [topological_ring R] (J : ideal R) : Prop :=
H = J.adic_topology

notation `is-`J`-adic` := is_ideal_adic J

lemma is_ideal_adic.mem_nhds_zero [topological_space R] [topological_ring R] {J : ideal R}
  (H : is-J-adic) {U : set R} : U ∈ 𝓝 (0 : R) ↔ ∃ n : ℕ, (J^n).carrier ⊆ U :=
begin
  dsimp [is_ideal_adic] at H,
  erw [H, subgroups_basis.mem_nhds_zero, set.exists_mem_range],
  exact iff.rfl
end

lemma adic_topology_pow (I : ideal R) {n : ℕ} (h : n > 0) : I.adic_topology = (I^n).adic_topology :=
begin
  sorry
end

/- lemma is_ideal_adic.nonarchimedean [topological_space R] [topological_ring R] {J : ideal R}
  (H : is-J-adic) : nonarchimedean R :=
begin
/-   dsimp [is_ideal_adic] at H,
  dsimp [nonarchimedean],
  intros U U_in,
  rw H at U_in,

  rcases subgroups_basis.mem_nhds_zero.mp U_in with ⟨G, G_in, hG⟩,
  exact ⟨⟨G, ⟨is_op A rfl G_in, subgroups_basis.sub_groups G_in⟩⟩, hG⟩

 -/  sorry
end -/
end ideal

class with_ideal (R : Type*) [comm_ring R] := (ideal : ideal R)

namespace with_ideal
open topological_add_group
variables [with_ideal R]

protected def topological_space : topological_space R := (ideal R).adic_topology

local attribute [instance] with_ideal.topological_space

protected lemma topological_ring : topological_ring R :=
sorry

local attribute [instance] with_ideal.topological_ring

protected lemma nonarchimedean : nonarchimedean R :=
begin

  sorry
end
end with_ideal

variables [topological_space R] [topological_ring R]

lemma is_ideal_adic_iff (J : ideal R) :
  is-J-adic ↔ (∀ n : ℕ, is_open (J^n).carrier) ∧ (∀ s ∈ nhds (0 : R), ∃ n : ℕ, (J^n).carrier ⊆ s) :=
begin
  /- split,
  { intro H,
    delta is_ideal_adic at H,
    erw H at *,
    split,
    { exact adic_ring.is_open_pow_ideal, },
    { intros s hs,
      erw ← is_subgroups_basis.nhds_zero (adic_basis J),
      exact hs, }, },
  { rintro ⟨H₁, H₂⟩,
    apply topological_add_group.ext,
    { apply @topological_ring.to_topological_add_group },
    { apply @topological_ring.to_topological_add_group (J.adic_ring) },
    { ext s,
      split; intro H,
      { exact (is_subgroups_basis.nhds_zero _ _).mpr (H₂ s H) },
      { rcases (is_subgroups_basis.nhds_zero _ _).mp H with ⟨n, hn⟩,
        rw mem_nhds_sets_iff,
        refine ⟨_, hn, H₁ n, (J^n).zero_mem⟩ } } } -/sorry
end

lemma is_ideal_adic_pow {J : ideal R} (h : is-J-adic) {n : ℕ} (hn : n > 0) :
  is-J^n-adic :=
begin
  rw is_ideal_adic_iff at h ⊢,
  split,
  { intro m, rw ← pow_mul, apply h.left },
  { intros V hV,
    cases h.right V hV with m hm,
    use m,
    refine set.subset.trans _ hm,
    cases n, { exfalso, exact nat.not_succ_le_zero 0 hn },
    rw [← pow_mul, nat.succ_mul],
    apply ideal.pow_le_pow,
    apply nat.le_add_left }
end

/- def adic_ring (I : ideal R) := R

namespace adic_ring
variable {I : ideal R}

instance : comm_ring I.adic_ring :=  by unfold adic_ring ; apply_instance
instance : ring_with_zero_nhd I.adic_ring := ideal.to_ring_with_zero_nhd I

instance : topological_space I.adic_ring := adic_topology I

instance : topological_ring I.adic_ring := ring_with_zero_nhd.is_topological_ring _

lemma nonarchimedean : topological_add_group.nonarchimedean I.adic_ring :=
is_subgroups_basis.nonarchimedean (adic_basis I)

-- The statement of the next lemma should be `is_open ((I^n).carrier : set I.adic_ring)
-- but R leaks through, and Lean asks for a topology on R instance of using the topology
-- we provided on I.adic_ring. Understanding why this happens here and elsewhere but not
-- everywhere would probably bring us a long way towards understanding our problems down the road.
lemma is_open_pow_ideal (n : ℕ) : @is_open I.adic_ring _ (I^n).carrier :=
-- The following mysteriously times out: `is_subgroups_basis.is_op (adic_basis I) n`, so let's @
@is_subgroups_basis.is_op _ _ ℕ _ (adic_basis I) _ n
end adic_ring
end ideal

section
open ideal topological_add_group
variables {R : Type*} [comm_ring R]

local attribute [instance, priority 0] ideal.is_subgroups_basis
def is_ideal_adic [H : topological_space R] [topological_ring R] (J : ideal R) : Prop :=
H = J.adic_topology

notation `is-`J`-adic` := is_ideal_adic J

lemma is_ideal_adic_iff [topological_space R] [topological_ring R] (J : ideal R) :
  is-J-adic ↔ (∀ n : ℕ, is_open (↑(J^n) : set R)) ∧ (∀ s ∈ nhds (0 : R), ∃ n : ℕ, ↑(J^n) ⊆ s) :=
begin
  split,
  { intro H,
    delta is_ideal_adic at H,
    erw H at *,
    split,
    { exact adic_ring.is_open_pow_ideal, },
    { intros s hs,
      erw ← is_subgroups_basis.nhds_zero (adic_basis J),
      exact hs, }, },
  { rintro ⟨H₁, H₂⟩,
    apply topological_add_group.ext,
    { apply @topological_ring.to_topological_add_group },
    { apply @topological_ring.to_topological_add_group (J.adic_ring) },
    { ext s,
      split; intro H,
      { exact (is_subgroups_basis.nhds_zero _ _).mpr (H₂ s H) },
      { rcases (is_subgroups_basis.nhds_zero _ _).mp H with ⟨n, hn⟩,
        rw mem_nhds_sets_iff,
        refine ⟨_, hn, H₁ n, (J^n).zero_mem⟩ } } }
end

variables (R) [topological_space R] [topological_ring R]

def is_adic : Prop := ∃ (J : ideal R), is-J-adic

variables {R}
lemma is_ideal_adic.nonarchimedean {J : ideal R} (h : is-J-adic) :
  nonarchimedean R :=
begin
  delta is_ideal_adic at h, unfreezeI, subst h,
  exact @adic_ring.nonarchimedean R _ J,
end

lemma is_adic.nonarchimedean (h : is_adic R) :
  nonarchimedean R :=
by { cases h with J hJ, exact hJ.nonarchimedean }

lemma is_ideal_adic_pow {J : ideal R} (h : is-J-adic) {n : ℕ} (hn : n > 0) :
  is-J^n-adic :=
begin
  rw is_ideal_adic_iff at h ⊢,
  split,
  { intro m, rw ← pow_mul, apply h.left },
  { intros V hV,
    cases h.right V hV with m hm,
    use m,
    refine set.subset.trans _ hm,
    cases n, { exfalso, exact nat.not_succ_le_zero 0 hn },
    rw [← pow_mul, nat.succ_mul],
    apply ideal.pow_le_pow,
    apply nat.le_add_left }
end

lemma exists_ideal_adic_subset (h : is_adic R) (U : set R) (hU : U ∈ nhds (0:R)) :
  ∃ I : ideal R, is-I-adic ∧ (I : set R) ⊆ U :=
begin
  cases h with J hJ,
  have H := (is_ideal_adic_iff J).mp hJ,
  cases H.right U hU with n hn,
  refine ⟨J^(n + 1), _, _⟩,
  { apply is_ideal_adic_pow hJ, apply nat.succ_pos },
  { refine set.subset.trans (J.pow_le_pow _) hn,
    apply nat.le_succ }
end
end-/
