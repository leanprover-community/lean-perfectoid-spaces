import data.list.basic
import topology.algebra.ring
import ring_theory.subring
import group_theory.subgroup
import data.padics
import ring_theory.localization

import for_mathlib.topological_rings
import power_bounded

-- f-adic rings are called Huber rings by Scholze.
-- Topological ring A contains on open subring A0 such that the subspace topology on A0 is
-- I-adic, where I is a finitely generated ideal of A0 .

local attribute [instance, priority 0] classical.prop_decidable

universes u v

section
variables (A : Type u) [comm_ring A] [topological_space A] [topological_ring A]

structure Huber_ring.pair_of_definition :=
(A₀   : set A)
[Hr   : is_subring A₀]
(Ho   : is_open A₀)
(J    : ideal A₀)
(fin  : ∃ (gen : set A₀) (fin : fintype gen), ideal.span gen = J)
(top  : @is_ideal_adic _ (subset.comm_ring) _ (topological_subring A₀) J)

class Huber_ring (A : Type u) extends comm_ring A, topological_space A, topological_ring A :=
(pod : nonempty $ Huber_ring.pair_of_definition A)

end

namespace Huber_ring

namespace pair_of_definition
open localization

variables {A : Type u} [comm_ring A] [topological_space A] [topological_ring A]

def away_subring (h : pair_of_definition A) (s : A) (T : set A) :
  set (away s) :=
let s_inv : away s := ((to_units ⟨s, ⟨1, by simp⟩⟩)⁻¹ : units (away s)) in
let E : set (away s) := {x | ∃ t ∈ T, x = of t * s_inv } in
ring.closure (of '' h.A₀ ∪ E)

instance away_subring.is_subring (h : pair_of_definition A) (s : A) (T : set A) :
  is_subring (away_subring h s T) :=
ring.is_subring

instance (h : pair_of_definition A) : is_subring h.A₀ := h.Hr

def away.of_subring (h : pair_of_definition A) (s : A) (T : set A) :
  h.A₀ → away_subring h s T :=
λ a, ⟨of a.val, ring.mem_closure $ or.inl ⟨_, a.property, rfl⟩⟩

instance away.of_subring.is_ring_hom (h : pair_of_definition A) (s : A) (T : set A) :
  is_ring_hom (away.of_subring h s T) :=
{ map_one := rfl,
  map_mul := λ a₁ a₂, subtype.val_injective $ of_mul _ _ _ _,
  map_add := λ a₁ a₂, subtype.val_injective $ of_add _ _ _ _, }

def away.of_subring.is_ring_hom' (h : pair_of_definition A) (s : A) (T : set A) :
  @is_ring_hom _ _ (comm_ring.to_ring _) (comm_ring.to_ring _) (away.of_subring h s T) :=
{ map_one := rfl,
  map_mul := λ a₁ a₂, subtype.val_injective $ of_mul _ _ _ _,
  map_add := λ a₁ a₂, subtype.val_injective $ of_add _ _ _ _, }

def away_ideal (h : pair_of_definition A) (s : A) (T : set A) :
  ideal (away_subring h s T) :=
@ideal.map _ _ _ _ (away.of_subring h s T) (away.of_subring.is_ring_hom' h s T) h.J

lemma away_ideal_fin (h : pair_of_definition A) (s : A) (T : set A) :
  ∃ (gen : set (away_subring h s T)) (fin : fintype gen), ideal.span gen = away_ideal h s T :=
begin
  rcases h.fin with ⟨gen, fin, span⟩,
  resetI,
  use away.of_subring h s T '' gen,
  split,
  { apply_instance },
  { have := @le_antisymm,
    sorry }
end

end pair_of_definition


variables {A : Type u} [Huber_ring A]

def is_ring_of_definition (A₀ : set A) : Prop :=
∃ pod : pair_of_definition A, A₀ = pod.A₀

instance is_ring_of_definition.is_subring {A₀ : set A} (h : is_ring_of_definition A₀) :
  is_subring A₀ :=
begin
  cases h with pod h,
  tactic.unfreeze_local_instances,
  subst h,
  exact pod.Hr
end

lemma is_adic_of_is_ring_of_definition (A₀ : set A) (h : is_ring_of_definition A₀) :
  @is_adic A₀
    (@subset.comm_ring _ _ _ $ is_ring_of_definition.is_subring h)
    _ (@topological_subring _ _ _ _ A₀ (is_ring_of_definition.is_subring h)) :=
begin
  cases h with pod h,
  tactic.unfreeze_local_instances,
  subst h,
  use [pod.J, pod.top]
end

lemma nonarchimedean : nonarchimedean A :=
begin
  rcases Huber_ring.pod A with ⟨A₀, H₁, H₂, J, Hfin, Htop⟩,
  resetI,
  apply nonarchimedean_of_nonarchimedean_subring A₀ H₂,
  exact Htop.nonarchimedean,
end


instance (p : ℕ) [p.prime] : Huber_ring (ℚ_[p]) :=
{ pod := ⟨{ A₀ := {x : ℚ_[p] | ∥x∥ ≤ 1},
  Hr  := sorry,
  Ho  := sorry,
  J   := sorry,
  fin := sorry,
  top := sorry } }




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
