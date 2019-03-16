import data.list.basic
import topology.algebra.ring
import ring_theory.algebra_operations
import group_theory.subgroup
import ring_theory.localization

import for_mathlib.topological_rings
import for_mathlib.rings
import for_mathlib.top_ring

import power_bounded

-- f-adic rings are called Huber rings by Scholze.
-- Topological ring A contains on open subring A0 such that the subspace topology on A0 is
-- I-adic, where I is a finitely generated ideal of A0 .

local attribute [instance, priority 0] classical.prop_decidable

universes u v

section
open set

structure Huber_ring.ring_of_definition
  (A₀ : Type*) [comm_ring A₀] [topological_space A₀] [topological_ring A₀]
  (A : Type*) [comm_ring A] [topological_space A] [topological_ring A]
  extends algebra A₀ A :=
(emb : embedding to_fun)
(hf  : is_open (range to_fun))
(J   : ideal A₀)
(fin : J.fg)
(top : is_ideal_adic J)

class Huber_ring (A : Type u) extends comm_ring A, topological_space A, topological_ring A :=
(pod : ∃ (A₀ : Type u) [comm_ring A₀] [topological_space A₀] [topological_ring A₀],
  by resetI; exact nonempty (Huber_ring.ring_of_definition A₀ A))

end

namespace Huber_ring

namespace ring_of_definition
open set localization algebra submodule

variables {A  : Type u} [comm_ring A ] [topological_space A ] [topological_ring A ]
variables (A₀ : Type u) [comm_ring A₀] [topological_space A₀] [topological_ring A₀]

variables [algebra A₀ A]
variables (T : set A) (s : A)

/-
Our goal is to define a topology on (away s), which is the localization of A at s.
This topology will depend on T, and should not depend on the ring of definition.
In the literature, this ring is commonly denoted with A(T/s) to indicate the
dependence on T. For the same reason, we start by defining a wrapper type that
includes T in its assumptions.
We will construct the topology on A(T/s) by showing that it is a Huber ring:
we construct a ring of definition that does depend on (h : ring_of_definition A₀ A).
-/

/--The localization at s, endowed with a topology that depends on T-/
def away (T : set A) (s : A) := (comap A₀ A (away s))

local notation `ATs` := away A₀ T s

instance away.comm_ring : comm_ring (ATs) :=
by delta away; apply_instance

instance : algebra A₀ (ATs) :=
by delta away; apply_instance

def T_over_s.aux : set (ATs) :=
let s_inv : ATs :=
  ((to_units ⟨s, ⟨1, by simp⟩⟩)⁻¹ : units ATs) in
{x | ∃ t ∈ T, x = of t * s_inv }

local notation `T_over_s` := T_over_s.aux A₀ T s

/--The ring of definition for the localization.-/
def D.aux := adjoin A₀ T_over_s

local notation `D` := D.aux A₀ T s

lemma away_comm_square :
  (D).val.comp (of_id A₀ D) = (to_comap A₀ A _ : A →ₐ[A₀] ATs).comp (of_id A₀ A) := rfl

-- lemma away_comm_square_linear :
--   (D).val.to_linear_map.comp (of_id A₀ D).to_linear_map =
--   (to_comap A₀ A _ : A →ₐ[A₀] ATs).to_linear_map.comp (of_id A₀ A).to_linear_map := rfl

variables (emb : embedding (of_id A₀ A : A₀ → A))
variables (open_range : is_open (range (of_id A₀ A : A₀ → A)))
variables (I₀ : ideal A₀) (top : is-I₀-adic)

set_option class.instance_max_depth 90

def J₀.aux : ideal D := I₀.map $ of_id A₀ D

local notation `J₀` := J₀.aux A₀ T s I₀

variable (A)
def I.aux (i : ℕ) : submodule A₀ A := submodule.map (of_id A₀ A).to_linear_map (I₀ ^ i)
variable {A}

local notation `I^` i := I.aux A A₀ I₀ i

include I₀
def J.aux (i : ℕ) : submodule D ATs :=
submodule.map (of_id D ATs).to_linear_map (by convert J₀ ^ i : submodule D D)
omit I₀

local notation `J^` i := J.aux A₀ T s I₀ i

instance adjoin.topological_space : topological_space (D) :=
(J₀).adic_topology

instance adjoin.topological_ring :
  @topological_ring D (adjoin.topological_space _ _ _ I₀) _ :=
by convert @adic_ring.topological_ring _ _ (J₀)

include emb open_range top
variables {A} {I₀}

lemma exists_image_mul_left_subset' (a : A) (i : ℕ) :
  ∃ (j : ℕ), (*) a '' ((of_id A₀ A) '' ↑(I₀ ^ j)) ⊆ (of_id A₀ A) '' ↑(I₀ ^ i) :=
begin
  rw is_ideal_adic_iff at top,
  cases top with H₁ H₂,
  simp only [set.image_subset_iff],
  apply H₂,
  apply mem_nhds_sets,
  apply emb.continuous,
  { apply continuous_mul_left,
    apply embedding_open;
    apply_assumption },
  { use [0, (I₀^i).zero_mem],
    simp [is_ring_hom.map_zero (algebra_map A)] }
end

lemma exists_image_mul_left_subset (a : A) (i : ℕ) :
  ∃ (j : ℕ), (map (lmul_left A₀ A a) I^j) ≤ I^i :=
begin
  apply exists_image_mul_left_subset' _ _ _ _ a i; assumption
end

omit emb open_range top

namespace away
open function linear_map

include emb open_range top

lemma exists_image_mul_left_subset.aux (a : A) (i : ℕ) :
  ∃ (j : ℕ), ((span _ {(of a : away A₀ T s)}) * J^j) ≤ J^i :=
begin
  cases exists_image_mul_left_subset A₀ emb open_range top a i with j hj,
  refine ⟨j, _⟩, -- change this to `use j` to get a deterministic timeout
  simp only [mul_left_span_singleton_eq_image],
  delta J.aux J₀.aux,
  erw ← @is_monoid_hom.map_pow _ _ _ _ (ideal.map _) ideal.map_is_monoid_hom,
  erw ← @is_monoid_hom.map_pow _ _ _ _ (ideal.map _) ideal.map_is_monoid_hom,
  rw le_def',
  rintros _ ⟨_, ⟨⟨x₀, hx₀, rfl⟩, rfl⟩⟩,
  apply submodule.span_induction hx₀,
  { intros m hm,
    refine set.image_subset _ ideal.subset_span _,
    have key_fact := submodule.map_mono hj,
    erw [← map_comp, ← map_comp _ (to_comap A₀ A _ : A →ₐ[A₀] ATs).to_linear_map,
      ← map_comp, map_lmul_left, comp_assoc,
      ← to_linear_map_comp, ← away_comm_square A₀ T s, to_linear_map_comp,
      ← comp_assoc, map_comp, map_comp, map_comp] at key_fact,
    apply key_fact,
    refine ⟨_, ⟨_, hm, rfl⟩, rfl⟩, },
  { repeat {rw linear_map.map_zero},
    apply submodule.zero_mem },
  { intros,
    repeat {rw linear_map.map_add},
    apply submodule.add_mem; assumption },
  { intros,
    repeat {rw linear_map.map_smul},
    apply submodule.smul_mem; assumption },
end

-- TODO(jmc): This needs the assumption that T.A is open.
-- I have not yet added that assumption.
lemma exists_image_mul_left_subset.aux' (s' : powers s) (i : ℕ) :
  ∃ (j : ℕ), ((span _ {(units.val (to_units s' : units ATs)⁻¹ : away A₀ T s)}) * J^j) ≤ J^i :=
begin
  delta J.aux,
  induction i with i ih,
  { erw [pow_zero, ideal.one_eq_top, map_top],
    simp only [mul_left_span_singleton_eq_image],
    sorry },
  { cases ih with j hj,
    refine ⟨j+1, _⟩,
    erw [pow_succ' _ j, pow_succ' _ i, submodule.map_mul],
    erw [← mul_assoc],
    convert mul_le_mul_left hj,
    erw [submodule.map_mul, mul_comm] }
end

end away

end ring_of_definition

end Huber_ring

namespace Huber_ring

variables {A : Type u} [Huber_ring A]

lemma nonarchimedean : nonarchimedean A :=
begin
  rcases Huber_ring.pod A with ⟨A₀, H₁, H₂, H₃, H₄, emb, hf, J, Hfin, Htop⟩,
  resetI,
  apply nonarchimedean_of_nonarchimedean_embedding (algebra_map A) emb hf,
  exact Htop.nonarchimedean,
end

instance power_bounded_subring.is_subring : is_subring (power_bounded_subring A) :=
power_bounded_subring.is_subring nonarchimedean

end Huber_ring

#exit
-- everything that follows is not yet refactored

lemma exists_image_mul_left_subset (a : away T s) (i : ℕ) :
  ∃ (j : ℕ), (*) a '' (h.away_f T s '' ↑(h.away_ideal T s ^ j)) ⊆
    h.away_f T s '' ↑(h.away_ideal T s ^ i) :=
begin
  apply localization.induction_on a,
  clear a, intros a s',
  rw [localization.mk_eq, mul_comm, mul_left_mul],
  conv { congr, funext, rw [image_comp], },
  cases exists_image_mul_left_subset.aux' h T s s' i with j₀ hj₀,
  cases exists_image_mul_left_subset.aux h T s a j₀ with j₁ hj₁,
  use j₁,
  refine set.subset.trans _ hj₀,
  apply set.image_subset,
  apply hj₁,
  exact le_refl _,
end

instance aux (n : ℕ) : is_add_subgroup (h.away_f T s '' ((h.away_ideal T s)^n).carrier) :=
@is_add_group_hom.image_add_subgroup _ _ _ _
  (h.away_f T s) (@is_ring_hom.is_add_group_hom _ _ _ _ subtype.val $ away_f.is_ring_hom h T s)
  _ (submodule.submodule_is_add_subgroup _)

instance : ring_with_zero_nhd (away T s) :=
of_subgroups (λ n : ℕ, h.away_f T s '' ((h.away_ideal T s)^n).carrier)
  (λ i j, ⟨i+j,
  begin
    erw set.image_inter subtype.val_injective,
    apply set.image_subset,
    rw pow_add,
    exact ideal.mul_le_inf,
  end⟩)
  (exists_image_mul_left_subset h T s)
  begin
    intros a i,
    sorry
  end
  begin
    intros i,
    use i,
    sorry
  end

instance : topological_space (away T s) :=
@ring_with_zero_nhd.topological_space (away T s) (away.ring_with_zero_nhd h T s)

instance : topological_ring (away T s) :=
@ring_with_zero_nhd.topological_ring (away T s) (away.ring_with_zero_nhd h T s)

end away

def away_ring_of_definition : ring_of_definition (h.away_subring T s) (away T s) :=
sorry

end ring_of_definition



/- KMB: I am commenting this out because it doesn't compile, I didn't write it,
and I don't know if we need it.

/-- An alternative definition. This deduces the property. The constructor is given below.
(Wedhorn, prop+def 6.1.) -/
lemma alt_def :
  ∃ U T : set A, T ⊆ U ∧ set.finite T ∧
  (filter.generate {U' : set A | ∃ n : pnat, U' = {x | ∃ y ∈ U, y^(n:ℕ) = x}} = (nhds 0)) ∧
  add_group.closure {y : A | ∃ (t ∈ T) (u ∈ U), y = t * u} =
  add_group.closure {y : A | ∃ (u₁ ∈ U) (u₂ ∈ U), y = u₁ * u₂} ∧
  add_group.closure {y : A | ∃ (t ∈ U) (u ∈ U), y = t * u} ⊆ U :=
begin
  rcases Huber_ring.pod A with ⟨⟨A₀, Hr, Ho, J, gen, fin, span, top⟩⟩,
  resetI,
  use [subtype.val '' J.carrier, subtype.val '' gen],
  have gensubJ : subtype.val '' gen ⊆ subtype.val '' J.carrier,
  { apply set.image_subset,
    rw ← span,
    convert ideal.subset_span, },
  refine ⟨gensubJ, set.finite_image _ ⟨fin⟩, _, _, _⟩,
  { apply le_antisymm,
    { sorry },
    { sorry } },
  { sorry },
  { haveI : is_add_subgroup J.carrier := J.submodule_is_add_subgroup,
    --have := @is_add_group_hom.image_add_subgroup _ _ _ _
    --subtype.val (subtype.val.is_add_group_hom) J.carrier,
    apply add_group.closure_subset, }
end
-/

end Huber_ring
