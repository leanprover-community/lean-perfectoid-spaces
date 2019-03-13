import data.list.basic
import topology.algebra.ring
import ring_theory.subring
import group_theory.subgroup
import ring_theory.localization

import for_mathlib.topological_rings
import for_mathlib.rings
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

def away_type (h : ring_of_definition A₀ A) (s : A) (T : set A) : Type u :=
let s_inv : away s := ((to_units ⟨s, ⟨1, by simp⟩⟩)⁻¹ : units (away s)) in
let E : set (away s) := {x | ∃ t ∈ T, x = of t * s_inv } in
ring.closure (of '' (range h.f) ∪ E)

instance away_subring.comm_ring (h : ring_of_definition A₀ A) (s : A) (T : set A) :
  comm_ring (away_type h s T) :=
by delta away_type; apply_instance

def away.of_subring (h : ring_of_definition A₀ A) (s : A) (T : set A) :
  A₀ → away_type h s T :=
λ a, ⟨of (h.f a), ring.mem_closure $ or.inl $ ⟨h.f a, mem_range_self a, rfl⟩⟩

instance away.of_subring.is_ring_hom (h : ring_of_definition A₀ A) (s : A) (T : set A) :
  is_ring_hom (away.of_subring h s T) :=
{ map_one := subtype.val_injective $ show of (h.f 1) = 1,
    by erw [@is_ring_hom.map_one _ _ _ _ h.f h.hom, of_one _ _],
  map_mul := λ a₁ a₂, subtype.val_injective $ show of (h.f _) = of (h.f _) * of (h.f _),
    by erw [@is_ring_hom.map_mul _ _ _ _ h.f h.hom, of_mul _ _],
  map_add := λ a₁ a₂, subtype.val_injective $ show of (h.f _) = of (h.f _) + of (h.f _),
    by erw [@is_ring_hom.map_add _ _ _ _ h.f h.hom, of_add _ _] }

def away_ideal (h : ring_of_definition A₀ A) (s : A) (T : set A) :
  ideal (away_type h s T) :=
h.J.map (away.of_subring h s T)

lemma away_ideal_fin (h : ring_of_definition A₀ A) (s : A) (T : set A) :
  ∃ (gen : set (away_type h s T)), finite gen ∧ ideal.span gen = away_ideal h s T :=
begin
  rcases h.fin with ⟨gen, fin, span⟩,
  resetI,
  use away.of_subring h s T '' gen,
  split,
  { apply finite_image _ fin, },
  { rw [← ideal.map_span _ _, span],
    refl, }
end

instance (h : ring_of_definition A₀ A) (s : A) (T : set A) :
  topological_space (away_type h s T) :=
(away_ideal h s T).adic_topology

instance (h : ring_of_definition A₀ A) (s : A) (T : set A) :
  topological_ring (away_type h s T) :=
adic_ring.topological_ring

-- jmc: the following definition is not yet possible
-- jmc: we first need a topological ring structure on (away s)

-- def away_ring_of_definition (h : ring_of_definition A₀ A) (s : A) (T : set A) :
--   ring_of_definition (away_type h s T) (away s) :=

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
