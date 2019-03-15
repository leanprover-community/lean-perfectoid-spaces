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
(fin : ∃ gen, finite gen ∧ ideal.span gen = J)
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

instance away.comm_ring : comm_ring (away A₀ T s) :=
by delta away; apply_instance

instance : algebra A₀ (away A₀ T s) :=
by delta away; apply_instance

def T_over_s.aux : set (away A₀ T s) :=
let s_inv : (away A₀ T s) :=
  ((to_units ⟨s, ⟨1, by simp⟩⟩)⁻¹ : units (away A₀ T s)) in
{x | ∃ t ∈ T, x = of t * s_inv }

local notation `T_over_s` := T_over_s.aux A₀ T s

/--The ring of definition for the localization.-/
def D.aux := adjoin A₀ T_over_s

local notation `D` := D.aux A₀ T s

variables (emb : embedding (algebra_map A : A₀ → A))
variables (open_range : is_open (range (algebra_map A : A₀ → A)))
variables (I₀ : ideal A₀) (top : is-I₀-adic)

set_option class.instance_max_depth 90
def J₀.aux : ideal D := I₀.map $ algebra_map _

local notation `J₀` := J₀.aux A₀ T s I₀

variable (A)
def I.aux (i : ℕ) : submodule A₀ A := submodule.map (linear_map A₀ A) (I₀ ^ i)
variable {A}

local notation `I^` i := I.aux A A₀ I₀ i

include I₀
def J.aux (i : ℕ) : submodule D (away A₀ T s) :=
submodule.map (linear_map D (away A₀ T s)) (by convert J₀ ^ i : submodule D D)
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
  ∃ (j : ℕ), (*) a '' ((algebra_map A : A₀ → A) '' ↑(I₀ ^ j)) ⊆
  (algebra_map A : A₀ → A) '' ↑(I₀ ^ i) :=
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
  ∃ (j : ℕ), (span _ {a} * I^j) ≤ I^i :=
begin
  show ∃ (j : ℕ), ↑(span _ {a} * I^j) ⊆ ↑(I^i),
  simp [mul_left_span_singleton_eq_image _ a],
  apply exists_image_mul_left_subset' _ _ _ _ a i; assumption
end

omit emb open_range top

namespace away
open function

include emb open_range top

lemma exists_image_mul_left_subset.aux (a : A) (i : ℕ) :
  ∃ (j : ℕ), ((span _ {(of a : away A₀ T s)}) * J^j) ≤ J^i :=
begin
  cases exists_image_mul_left_subset A₀ emb open_range top a i with j hj,
  use j,
end

lemma exists_image_mul_left_subset.aux' (a : A) (i : ℕ) :
  ∃ (j : ℕ), (*) (of a : away T s) '' (h.away_f T s '' ↑(h.away_ideal T s ^ j)) ⊆
    h.away_f T s '' ↑(h.away_ideal T s ^ i) :=
begin
  cases exists_image_mul_left_subset h a i with j₀ hj₀,
  use j₀,
  intros j hj,
  erw ← @is_monoid_hom.map_pow _ _ _ _ (ideal.map _) ideal.map_is_monoid_hom,
  erw ← @is_monoid_hom.map_pow _ _ _ _ (ideal.map _) ideal.map_is_monoid_hom,
  rintros _ ⟨_, ⟨⟨x₀, hx₀, rfl⟩, rfl⟩⟩,
  apply submodule.span_induction hx₀,
  { intros x hx,
    delta away_ideal ideal.map,
    refine set.image_subset _ ideal.subset_span _,
    have key_fact := set.image_subset (of : A → away T s) (hj₀ j hj),
    rw [← image_comp of, ← image_comp of] at key_fact,
    rw [is_ring_hom.map_mul_left (of : A → away T s)] at key_fact,
    rw [← image_comp, comp.assoc, h.away_comm_square T s, ← comp.assoc] at key_fact,
    rw [image_comp, image_comp (h.away_f T s)] at key_fact,
    apply key_fact,
    use [x, hx] },
  { use [0, (ideal.map _ _).zero_mem],
    rw @is_ring_hom.map_zero _ _ _ _ (h.away_f _ _) (away_f.is_ring_hom h T s),
    exact (mul_zero _).symm },
  { rintros x y ⟨x', ⟨hx', hx⟩⟩ ⟨y', ⟨hy', hy⟩⟩,
    use [x' + y', ideal.add_mem (ideal.map _ _) hx' hy'],
    rw @is_ring_hom.map_add _ _ _ _ (h.away_f _ _) (away_f.is_ring_hom h T s),
    rw @is_ring_hom.map_add _ _ _ _ (h.away_f _ _) (away_f.is_ring_hom h T s),
    rw [hx, hy],
    exact (left_distrib _ _ _).symm },
  { rintros a' x ⟨x', ⟨hx', hx⟩⟩,
    use [a' * x', ideal.mul_mem_left (ideal.map _ _) hx'],
    rw smul_eq_mul,
    rw @is_ring_hom.map_mul _ _ _ _ (h.away_f _ _) (away_f.is_ring_hom h T s),
    rw @is_ring_hom.map_mul _ _ _ _ (h.away_f _ _) (away_f.is_ring_hom h T s),
    rw [hx, ← mul_assoc, mul_comm _ (of a), mul_assoc] }
end

lemma exists_image_mul_left_subset.aux' (s' : powers s) (i : ℕ) :
  ∃ (j : ℕ), (*) (units.val (to_units s' : units (away T s))⁻¹ : away T s) ''
    (away_f h T s '' ↑(away_ideal h T s ^ j)) ⊆ away_f h T s '' ↑(away_ideal h T s ^ i) :=
begin
  induction i with i ih,
  { sorry },
  { cases ih with j hj,
    use j+1,
    sorry }
end

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

variables {A : Type u} [Huber_ring A]

lemma nonarchimedean : nonarchimedean A :=
begin
  rcases Huber_ring.pod A with ⟨A₀, H₁, H₂, H₃, f, hom, emb, hf, J, Hfin, Htop⟩,
  resetI,
  apply nonarchimedean_of_nonarchimedean_embedding f emb hf,
  exact Htop.nonarchimedean,
end

instance power_bounded_subring.is_subring : is_subring (power_bounded_subring A) :=
power_bounded_subring.is_subring nonarchimedean


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
