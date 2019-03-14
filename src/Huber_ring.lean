import data.list.basic
import topology.algebra.ring
import ring_theory.subring
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
  (A : Type*) [comm_ring A] [topological_space A] [topological_ring A] :=
(f : A₀ → A)
(hom : is_ring_hom f)
(emb : embedding f)
(hf  : is_open (range f))
(J   : ideal A₀)
(fin : ∃ gen, finite gen ∧ ideal.span gen = J)
(top : is_ideal_adic J)

class Huber_ring (A : Type u) extends comm_ring A, topological_space A, topological_ring A :=
(pod : ∃ (A₀ : Type u) [comm_ring A₀] [topological_space A₀] [topological_ring A₀],
  by resetI; exact nonempty (Huber_ring.ring_of_definition A₀ A))

end

namespace Huber_ring

namespace ring_of_definition
open set localization

variables {A  : Type u} [comm_ring A ] [topological_space A ] [topological_ring A ]
variables {A₀ : Type u} [comm_ring A₀] [topological_space A₀] [topological_ring A₀]
variables (h : ring_of_definition A₀ A) (T : set A) (s : A)

/-
Our goal is to define a topology on (away s), which is the localization of A at s.
This topology will depend on T, and should not depend on the ring of definition
(h : ring_of_definition A₀ A). In the literature, this ring is commonly denoted with
A(T/s) to indicate the dependence on T. For the same reason, we start by defining a
wrapper type that includes T in its assumptions.
We will construct the topology on A(T/s) by showing that it is a Huber ring: we construct
a ring of definition that does depend on (h : ring_of_definition A₀ A).
-/

/--The localization at s, endowed with a topology that depends on T-/
def away (T : set A) (s : A) := away s

instance away.comm_ring : comm_ring (away T s) :=
by delta away; apply_instance

/--The ring of definition for the localization.-/
def away_subring : Type u :=
let s_inv : away T s := ((to_units ⟨s, ⟨1, by simp⟩⟩)⁻¹ : units (away T s)) in
let E : set (away T s) := {x | ∃ t ∈ T, x = of t * s_inv } in
ring.closure (of '' (range h.f) ∪ E)

instance away_subring.comm_ring : comm_ring (h.away_subring T s) :=
by delta away_subring; by apply_instance

def away_f : h.away_subring T s → away T s := subtype.val

instance away_f.is_ring_hom : is_ring_hom (h.away_f T s) :=
@is_ring_hom.is_ring_hom _ _ _ ring.is_subring

def away_of_subring : A₀ → h.away_subring T s :=
λ a, ⟨(h.f a), ring.mem_closure $ or.inl $ ⟨h.f a, mem_range_self a, rfl⟩⟩

instance away.of_subring.is_ring_hom :
  is_ring_hom (h.away_of_subring T s) :=
{ map_one := subtype.val_injective $ show of (h.f 1) = 1,
    by erw [@is_ring_hom.map_one _ _ _ _ h.f h.hom, of_one _ _],
  map_mul := λ a₁ a₂, subtype.val_injective $ show of (h.f _) = of (h.f _) * of (h.f _),
    by erw [@is_ring_hom.map_mul _ _ _ _ h.f h.hom, of_mul _ _],
  map_add := λ a₁ a₂, subtype.val_injective $ show of (h.f _) = of (h.f _) + of (h.f _),
    by erw [@is_ring_hom.map_add _ _ _ _ h.f h.hom, of_add _ _] }

lemma away_comm_square :
  (of : A → away T s) ∘ h.f = h.away_f T s ∘ h.away_of_subring T s := rfl

def away_ideal : ideal (h.away_subring T s) :=
h.J.map (h.away_of_subring T s)

lemma away_ideal_fin :
  ∃ (gen : set (h.away_subring T s)), finite gen ∧ ideal.span gen = h.away_ideal T s :=
begin
  rcases h.fin with ⟨gen, fin, span⟩,
  resetI,
  use h.away_of_subring T s '' gen,
  split,
  { apply finite_image _ fin, },
  { rw [← ideal.map_span _ _, span],
    refl, }
end

namespace away_subring

instance : topological_space (h.away_subring T s) :=
(h.away_ideal T s).adic_topology

instance : topological_ring (h.away_subring T s) :=
adic_ring.topological_ring

end away_subring

lemma exists_image_mul_left_subset (a : A) (i : ℕ) :
  ∃ (j₀ : ℕ), ∀ j ≥ j₀, (*) a '' (h.f '' ↑(h.J ^ j)) ⊆ h.f '' ↑(h.J ^ i) :=
begin
  rcases h with ⟨f,hom,emb,hf,J,fin,top⟩,
  cases emb with inj ind,
  tactic.unfreeze_local_instances,
  subst ind,
  resetI,
  letI : topological_space A₀ := topological_space.induced f ‹topological_space A›,
  rw is_ideal_adic_iff at top,
  cases top with H₁ H₂,
  -- proper start of the proof
  show ∃ (j₀ : ℕ), ∀ j ≥ j₀, (*) a '' (f '' ↑(J ^ j)) ⊆ f '' ↑(J ^ i),
  simp only [set.image_subset_iff],
  have key_fact : ∀ (s : set A₀), s ∈ nhds (0 : A₀) → ∃ (j₀ : ℕ), ∀ j ≥ j₀, ↑(J^j) ⊆ s :=
  begin
    intros s hs,
    cases H₂ s hs with j₀ hj₀,
    use j₀,
    intros j hj,
    apply set.subset.trans _ hj₀,
    cases nat.exists_eq_add_of_le hj with k hk,
    rw [hk, pow_add],
    transitivity,
    { exact ideal.mul_le_inf },
    { rw ← submodule.le_def,
      exact lattice.inf_le_left }
  end,
  apply key_fact,
  rw mem_nhds_induced,
  refine ⟨_, _, set.subset.refl _⟩,
  apply mem_nhds_sets,
  { apply continuous_mul_left _,
    apply embedding_open ⟨inj, rfl⟩ hf (H₁ _),
    apply_instance },
  { use [0, (J^i).zero_mem],
    simp [is_ring_hom.map_zero f] }
end

namespace away
open function

lemma exists_image_mul_left_subset.aux (a : A) (i : ℕ) :
  ∃ (j₀ : ℕ), ∀ j ≥ j₀, (*) (of a : away T s) '' (h.away_f T s '' ↑(h.away_ideal T s ^ j)) ⊆
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
