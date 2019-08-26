import tactic.converter.interactive
import topology.algebra.ring

import for_mathlib.data.set.basic
import for_mathlib.topology
import for_mathlib.rings

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
  rw induced_inf
end
end topological_space

@[simp]
lemma division_ring.inv_val_eq_inv {α : Type*} [division_ring α] (x : units α) :(x : α)⁻¹ = x.inv :=
begin
  rw (show x.inv = (x⁻¹ : units α), from rfl),
  rw ←one_div_eq_inv,
  symmetry,
  apply eq_one_div_of_mul_eq_one,
  exact x.mul_inv
end

namespace topological_ring
open topological_space function
variables (R : Type*) [ring R]

lemma units.coe_inj : injective (coe : units R → R) :=
λ x y h, units.ext h

variables  [topological_space R]

-- This is not a global instance. Instead we introduced a class `induced_units` asserting
-- something equivalent to this construction holds
def topological_space_units : topological_space (units R) := induced units.val ‹_›

class induced_units (R : Type*) [ring R] [topological_space R] [t : topological_space $ units R] :
  Prop :=
(top_eq : t = induced (coe : units R → R) ‹_›)

variables [ring R] [topological_space R] [topological_space $ units R]

lemma induced_units.continuous_coe [induced_units R] : continuous (coe : units R → R) :=
(induced_units.top_eq R).symm ▸ continuous_induced_dom

lemma units_embedding [topological_space $ units R] [induced_units R] :
  embedding (units.val : units R → R) :=
{ induced := induced_units.top_eq R,
  inj := units.coe_inj _ }

instance top_monoid_units [topological_ring R] [topological_space $ units R] [induced_units R] :
  topological_monoid (units R) :=
⟨begin
  let mulR := (λ (p : R × R), p.1*p.2),
  let mulRx := (λ (p : units R × units R), p.1*p.2),
  have key : coe ∘ mulRx = mulR ∘ (λ p, (p.1.val, p.2.val)), from rfl,
  rw [continuous_iff_le_induced, induced_units.top_eq R, prod_induced_induced,
      induced_compose, key, ← induced_compose],
  apply induced_mono,
  rw ← continuous_iff_le_induced,
  exact continuous_mul',
end⟩
end topological_ring

variables (K : Type*) [division_ring K] [topological_space K]

/-- A topological division ring is a division ring with a topology where all operations are
    continuous, including inversion. -/
class topological_division_ring extends topological_ring K : Prop :=
(continuous_inv : ∀ x : K, x ≠ 0 → continuous_at (λ x : K, x⁻¹ : K → K) x)

namespace topological_division_ring
open filter set
/-
In this section, we show that units of a topological division ring endowed with the
induced topology form a topological group. These are not global instances because
one could want another topology on units. To turn on this feature, use:

```lean
local attribute [instance]
topological_ring.topological_space_units topological_division_ring.units_top_group
```
-/

variables [topological_division_ring K]

local attribute [instance] topological_ring.topological_space_units

def induced_units : topological_ring.induced_units K := ⟨rfl⟩
local attribute [instance] induced_units

def units_top_group : topological_group (units K) :=
{ continuous_inv := begin
     have : (units.val : units K → K) ∘ (λx, x⁻¹ : units K → units K) = (λx, x⁻¹ : K → K) ∘ (coe : units K → K),
      by { ext, apply units.inv_eq_inv },
     rw continuous_iff_continuous_at,
     intros x,
     rw [continuous_at, nhds_induced, nhds_induced, tendsto_iff_comap, comap_comm this],
     apply comap_mono,
     rw ← tendsto_iff_comap,
     convert topological_division_ring.continuous_inv x.val x.ne_zero,
     exact x.inv_eq_inv
   end ,
  ..topological_ring.top_monoid_units K}

local attribute [instance] units_top_group

lemma continuous_units_inv : continuous (λ x, x.inv : units K → K) :=
begin
  change continuous (coe ∘ (λ x, x⁻¹ : units K → units K)),
  refine (topological_ring.induced_units.continuous_coe K).comp _,
  exact continuous_inv',
end
end topological_division_ring
