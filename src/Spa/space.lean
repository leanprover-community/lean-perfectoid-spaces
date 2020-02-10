import continuous_valuations
import Huber_pair

/-!
# The adic spectrum as a topological space

In this file we define a structure (`rational_open_data`) that will parameterise
a basis for the topology on the adic spectrum of a Huber pair.
-/

open_locale classical
local attribute [instance] set.pointwise_mul_comm_semiring
local attribute [instance] set.smul_set_action

local postfix `⁺` : 66 := λ A : Huber_pair, A.plus

variables {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]

-- We reserve the name `Spa` (with upper case `S`) for the bundled adic spectrum (`adic_space.lean`)
/-- The space underlying the adic spectrum of a Huber pair (A,A⁺)
consists of all the equivalence classes of valuations that are continuous
and whose value on the ring A⁺ is ≤ 1. [Wedhorn, Def 7.23]. -/
definition spa (A : Huber_pair) : Type :=
{v : Spv A // v.is_continuous ∧ ∀ r : A⁺, v (algebra_map A r) ≤ 1}

/--The equivalence class of a valuation is contained in spa
if and only if the valuation is continuous and its values on the ring A⁺ are ≤ 1,
since these properties are constant on equivalence classes.-/
lemma mk_mem_spa {A : Huber_pair} {v : valuation A Γ₀} :
  Spv.mk v ∈ {v : Spv A | v.is_continuous ∧ ∀ r : A⁺, v (algebra_map A r) ≤ 1} ↔
  v.is_continuous ∧ ∀ r : A⁺, v (algebra_map A r) ≤ 1 :=
begin
  apply and_congr,
  { exact (Spv.out_mk v).is_continuous_iff, },
  { apply forall_congr,
    intro r,
    simpa using (Spv.out_mk v) (algebra_map A r) 1, }
end

namespace spa
open set algebra
variables {A : Huber_pair}

/-- The coercion from the adic spectrum of a Huber pair to the ambient valuation spectrum.-/
instance : has_coe (spa A) (Spv A) := ⟨subtype.val⟩

@[ext]
lemma ext (v₁ v₂ : spa A) (h : (Spv.out ↑v₁).is_equiv (Spv.out (↑v₂ : Spv A))) :
  v₁ = v₂ :=
subtype.val_injective $ Spv.ext _ _ h

lemma ext_iff {v₁ v₂ : spa A} :
  v₁ = v₂ ↔ ((Spv.out ↑v₁).is_equiv (Spv.out (↑v₂ : Spv A))) :=
by rw [subtype.coe_ext, Spv.ext_iff]

/-- The value monoid of a random representative valuation of a point in the adic spectrum. -/
abbreviation out_Γ₀ (v  : spa A) := Spv.out_Γ₀ (v : Spv A)

/-- A valuation in the adic spectrum is continuous. -/
lemma is_continuous (v : spa A) : Spv.is_continuous (v : Spv A) := v.property.left

/-- The valuation of an integral element is at most 1. -/
lemma map_plus (v : spa A) (a : (A⁺)) : v (algebra_map A a) ≤ 1 := v.property.right a

/-- The valuation of a unit of the ring of integral elements is 1. -/
@[simp] lemma map_unit (v : spa A) (u : units (A⁺)) :
  v ((algebra_map A : (A⁺) → A) u) = 1 :=
begin
  have h₁ := map_plus v u,
  have h₂ := map_plus v (u⁻¹ : _),
  have := actual_ordered_comm_monoid.mul_eq_one_iff_of_le_one' h₁ h₂,
  apply (this.mp _).left,
  erw ← valuation.map_mul,
  rw ← is_ring_hom.map_mul (algebra_map A : (A⁺) → A),
  simp only [units.mul_inv, algebra.map_one, valuation.map_one]
end

-- We are now going to setup the topology on `spa A`.
-- A basis of the topology is indexed by the following data:

/--A rational open subset of `spa A` is indexed by:
* an element s of A, and
* a finite set T ⊆ A that generates an open ideal in A.

In the literature, these sets are commonly denoted by D(T,s).-/
structure rational_open_data (A : Huber_pair) :=
(s : A)
(T : set A)
[Tfin : fintype T]
(Hopen : is_open ((ideal.span T) : set A))

namespace rational_open_data
variables (r : rational_open_data A)

attribute [instance] Tfin

@[ext]
lemma ext {r₁ r₂ : rational_open_data A} (hs : r₁.s = r₂.s) (hT : r₁.T = r₂.T) :
  r₁ = r₂ :=
begin
  cases r₁, cases r₂,
  congr; assumption
end

/--The subset of the adic spectrum associated with the data for a rational open subset.

In the literature, these sets are commonly denoted by D(T,s).-/
def open_set (r : rational_open_data A) : set (spa A) :=
{v : spa A | (∀ t ∈ r.T, (v t ≤ v r.s)) ∧ (v r.s ≠ 0)}

variable (A)

/--The rational open subset covering the entire adic spectrum.-/
def univ : rational_open_data A :=
{ s := 1,
  T := {1},
  Hopen := by { rw ideal.span_singleton_one, exact is_open_univ } }

variable {A}

@[simp] lemma univ_s : (univ A).s = 1 := rfl

@[simp] lemma univ_T : (univ A).T = {1} := rfl

@[simp] lemma univ_open_set :
  (univ A).open_set = set.univ :=
begin
  rw eq_univ_iff_forall,
  intros v,
  split,
  { intros t ht,
    erw mem_singleton_iff at ht,
    rw [ht, univ_s], },
  { erw [univ_s, Spv.map_one],
    exact one_ne_zero }
end

/--The rational open subset D(T,s) is the same as D(T ∪ {s}, s).-/
noncomputable def insert_s (r : rational_open_data A) : rational_open_data A :=
{ s := r.s,
  T := insert r.s r.T,
  Hopen := submodule.is_open_of_open_submodule
    ⟨ideal.span (r.T), r.Hopen, ideal.span_mono $ set.subset_insert _ _⟩ }

@[simp] lemma insert_s_s (r : rational_open_data A) :
(insert_s r).s = r.s := rfl

@[simp] lemma insert_s_T (r : rational_open_data A) :
(insert_s r).T = insert r.s r.T := rfl

@[simp] lemma insert_s_open_set (r : rational_open_data A) :
(insert_s r).open_set = r.open_set :=
begin
  ext v,
  split; rintros ⟨h₁, h₂⟩; split; try { exact h₂ }; intros t ht,
  { apply h₁ t,
    exact mem_insert_of_mem _ ht },
  { cases ht,
    { rw [ht, insert_s_s], },
    { exact h₁ t ht } },
end

lemma mem_insert_s (r : rational_open_data A) :
r.s ∈ (insert_s r).T := by {left, refl}

/-- Auxilliary definition for the intersection of two rational open sets.-/
noncomputable def inter_aux (r1 r2 : rational_open_data A) : rational_open_data A :=
{ s := r1.s * r2.s,
  T := r1.T * r2.T,
  Tfin := set.pointwise_mul_fintype _ _,
  Hopen :=
  begin
    rcases Huber_ring.exists_pod_subset _ (mem_nhds_sets r1.Hopen $ ideal.zero_mem $ ideal.span r1.T)
      with ⟨A₀, _, _, _, ⟨_, emb, I, fg, top⟩, hI⟩,
    dsimp only at hI,
    resetI,
    rw is_ideal_adic_iff at top,
    cases top.2 (algebra_map A ⁻¹' ↑(ideal.span r2.T)) _ with n hn,
    { apply submodule.is_open_of_open_submodule,
      use ideal.map (of_id A₀ A) (I^(n+1)),
      refine ⟨is_open_ideal_map_open_embedding emb _ (top.1 (n+1)), _⟩,
      delta ideal.span,
      erw [pow_succ, ideal.map_mul, ← submodule.span_mul_span],
      apply submodule.mul_le_mul,
      { exact (ideal.span_le.mpr hI) },
      { rw ← image_subset_iff at hn,
        exact (ideal.span_le.mpr hn) } },
    { apply emb.continuous.tendsto,
      rw show algebra.to_fun A (0:A₀) = 0,
      { haveI : is_ring_hom (algebra.to_fun A : A₀ → A) := algebra.is_ring_hom,
        apply is_ring_hom.map_zero },
      exact (mem_nhds_sets r2.Hopen $ ideal.zero_mem $ ideal.span r2.T) }
  end }

/--The intersection of two rational open sets is a rational open set.-/
noncomputable def inter (r1 r2 : rational_open_data A) : rational_open_data A :=
inter_aux (rational_open_data.insert_s r1) (rational_open_data.insert_s r2)

@[simp] lemma inter_s (r1 r2 : rational_open_data A) :
  (r1.inter r2).s = r1.s * r2.s := rfl

@[simp] lemma inter_T (r1 r2 : rational_open_data A) :
  (r1.inter r2).T = (insert r1.s r1.T) * (insert r2.s r2.T) := rfl

lemma inter_open_set (r1 r2 : rational_open_data A) :
(inter r1 r2).open_set = r1.open_set ∩ r2.open_set :=
begin
  rw [← insert_s_open_set r1, ← insert_s_open_set r2],
  apply le_antisymm,
  {  rintros v ⟨hv, hs⟩,
    have vmuls : v (r1.s * r2.s) = v r1.s * v r2.s := valuation.map_mul _ _ _,
    have hs₁ : v r1.s ≠ 0 := λ H, by simpa [-coe_fn_coe_base, vmuls, H] using hs,
    have hs₂ : v r2.s ≠ 0 := λ H, by simpa [-coe_fn_coe_base, vmuls, H] using hs,
    split; split; try { assumption };
    intros t ht,
    { suffices H : v t * v r2.s ≤ v r1.s * v r2.s,
      { simpa [hs₂, mul_assoc, -coe_fn_coe_base] using
          linear_ordered_structure.mul_le_mul_right H (group_with_zero.mk₀ _ hs₂)⁻¹, },
      { simpa using hv (t * r2.s) ⟨t, ht, r2.s, mem_insert_s r2, rfl⟩, } },
    { suffices H : v r1.s * v t ≤ v r1.s * v r2.s,
      { simpa [hs₁, mul_assoc, -coe_fn_coe_base] using
          linear_ordered_structure.mul_le_mul_left H (group_with_zero.mk₀ _ hs₁)⁻¹, },
      { simpa using hv (r1.s * t) ⟨r1.s, mem_insert_s r1, t, ht, rfl⟩, } } },
  { rintros v ⟨⟨hv₁, hs₁⟩, ⟨hv₂, hs₂⟩⟩,
    split,
    { rintros t ⟨t₁, ht₁, t₂, ht₂, rfl⟩,
      convert le_trans
        (linear_ordered_structure.mul_le_mul_right (hv₁ t₁ ht₁) _)
        (linear_ordered_structure.mul_le_mul_left  (hv₂ t₂ ht₂) _);
      apply valuation.map_mul },
    { assume eq_zero, simp at eq_zero, tauto }, }
end

lemma inter_symm (r1 r2 : rational_open_data A) :
  r1.inter r2 = r2.inter r1 :=
ext (mul_comm _ _) (mul_comm _ _)

end rational_open_data

variable (A)

/--The basis for the topology on the adic spectrum, consisting of rational open sets.-/
def rational_basis := {U : set (spa A) | ∃ r : rational_open_data A, U = r.open_set}

/--The topology on the adic spectrum, generated by rational open sets.-/
instance : topological_space (spa A) :=
topological_space.generate_from (rational_basis A)

variable {A}

/--The rational open sets form a basis for the topology on the adic spectrum.-/
lemma rational_basis.is_basis : topological_space.is_topological_basis (rational_basis A) :=
begin
  refine ⟨_, _, rfl⟩,
  { rintros _ ⟨r₁, rfl⟩ _ ⟨r₂, rfl⟩ x hx,
    refine ⟨_, ⟨_, (rational_open_data.inter_open_set r₁ r₂).symm⟩, hx, subset.refl _⟩, },
  { apply subset.antisymm (subset_univ _) (subset_sUnion_of_mem _),
    exact ⟨_, rational_open_data.univ_open_set.symm⟩ }
end

end spa
