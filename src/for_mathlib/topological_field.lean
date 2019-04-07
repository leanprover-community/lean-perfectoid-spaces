import tactic.converter.interactive
import topology.algebra.ring

open topological_space

namespace topological_space
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [topological_space β] [topological_space δ]

/-- A product of induced topologies is induced by the product map -/
lemma prod_induced_induced (f : α → β) (g : γ → δ) :
  @prod.topological_space _ _ (induced f ‹_›) (induced g ‹_›) = induced (λ p, (f p.1, g p.2)) prod.topological_space :=
begin
  letI := induced f ‹_›, letI := induced g ‹_›,
  set fxg := (λ p : α × γ, (f p.1, g p.2)),
  have key1 : f ∘ (prod.fst : α × γ → α) = (prod.fst : β × δ → β) ∘ fxg, from rfl,
  have key2 : g ∘ (prod.snd : α × γ → γ) = (prod.snd : β × δ → δ) ∘ fxg, from rfl,
  unfold prod.topological_space, -- product topology is a sup of induced topologies
  -- so let's be functorial
  conv_lhs {
    rw [induced_compose, induced_compose, key1, key2],
    congr, rw ← induced_compose, skip, rw ← induced_compose, },
  rw induced_sup
end
end topological_space

namespace topological_ring
open topological_space function
variables (R : Type*) [ring R]

lemma units.coe_inj : injective (coe : units R → R) :=
λ x y h, units.ext h

variables  [topological_space R]

instance : topological_space (units R) := induced units.val ‹_›

lemma units_embedding : embedding (units.val : units R → R) :=
⟨units.coe_inj _, rfl⟩

instance top_monoid_units [topological_ring R] : topological_monoid (units R) :=
⟨begin
  let mulR := (λ (p : R × R), p.1*p.2),
  let mulRx := (λ (p : units R × units R), p.1*p.2),
  have key : units.val ∘ mulRx = mulR ∘ (λ p, (p.1.val, p.2.val)), from rfl,
  rw continuous_iff_induced_le,
  unfold topological_ring.topological_space,
  rw [induced_compose, key, ← induced_compose, prod_induced_induced],
  apply induced_mono,
  rw ← continuous_iff_induced_le,
  exact continuous_mul',
end⟩
end topological_ring

variables (K : Type*) [division_ring K] [topological_space K]

/-- A topological division ring is a division ring with a topology where all operations are
    continuous, including inversion. -/
class topological_division_ring extends topological_ring K : Prop :=
(continuous_inv : continuous (λa : units K, a⁻¹))

namespace topological_division_ring

variables [topological_division_ring K]

instance units_top_group : topological_group (units K) :=
{ continuous_inv := topological_division_ring.continuous_inv K,
  ..topological_ring.top_monoid_units K}

end topological_division_ring
