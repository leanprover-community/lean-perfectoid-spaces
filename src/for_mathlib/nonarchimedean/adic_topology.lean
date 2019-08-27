import for_mathlib.nonarchimedean.basic
import for_mathlib.nonarchimedean.is_subgroups_basis

local prefix 𝓝:100 := nhds

variables {R : Type*} [comm_ring R]

open set lattice topological_add_group submodule

namespace ideal

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
end ideal

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

lemma is_ideal_adic_iff [topological_space R] [topological_ring R] {J : ideal R} :
  is-J-adic ↔ (∀ n : ℕ, is_open (J^n).carrier) ∧ (∀ s ∈ nhds (0 : R), ∃ n : ℕ, (J^n).carrier ⊆ s) :=
begin
  split,
  { intro H,
    split,
    { intro n,
       letI := ideal.adic_basis J,
      refine subgroups_basis.is_op R H (set.mem_range_self _) },
    { intros s hs,
      exact (is_ideal_adic.mem_nhds_zero H).mp hs } },
  { rintro ⟨H₁, H₂⟩,
    apply topological_add_group.ext,
    { apply @topological_ring.to_topological_add_group },
    { apply subgroups_basis.is_topological_add_group },
    { ext s,
      letI := ideal.adic_basis J,
      split; intro H,
      { rw subgroups_basis.mem_nhds_zero,
        cases H₂ s H with n hn,
        use [(J ^ n).carrier, mem_range_self _, hn] },
      { rcases subgroups_basis.mem_nhds_zero.mp H with  ⟨_, ⟨n, rfl⟩, hn⟩,
        rw mem_nhds_sets_iff,
        refine ⟨_, hn, H₁ n, (J^n).zero_mem⟩ } } }
end

lemma is_ideal_adic.nonarchimedean [topological_space R] [topological_ring R] {J : ideal R}
  (H : is-J-adic) : nonarchimedean R :=
begin
  intros U U_in,
  rcases (is_ideal_adic.mem_nhds_zero H).mp U_in with ⟨n, hn⟩,
  exact ⟨⟨(J^n).carrier,
         ⟨(is_ideal_adic_iff.mp H).left _, submodule.submodule_is_add_subgroup (J ^ n)⟩⟩,
         hn⟩,
end

class with_ideal (R : Type*) [comm_ring R] := (ideal : ideal R)

namespace with_ideal
open topological_add_group
variables [with_ideal R]

protected def topological_space : topological_space R := (ideal R).adic_topology

local attribute [instance] with_ideal.topological_space

protected lemma topological_ring : topological_ring R :=
begin
  letI := ideal.adic_basis (with_ideal.ideal R),
  exact ring_filter_basis.is_topological_ring _ rfl
end


local attribute [instance] with_ideal.topological_ring

protected lemma nonarchimedean : nonarchimedean R :=
by apply subgroups_basis.nonarchimedean
end with_ideal

variables [topological_space R] [topological_ring R]


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

variables (R)

def is_adic : Prop := ∃ (J : ideal R), is-J-adic
