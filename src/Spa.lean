import continuous_valuations
import Huber_pair 

universes u₁ u₂ u₃

local attribute [instance] classical.prop_decidable

open set

-- Wedhorn def 7.23.
definition Spa (A : Huber_pair) : set (Spv A) :=
Spv.lift (λ v : Valuation A, v.is_continuous ∧ ∀ r, r ∈ A⁺ → v r ≤ 1)
(λ v₁ v₂ heq,
begin
  ext, split; intro; split,
  { exact Valuation.is_continuous_of_equiv_is_continuous heq a.left },
  { rw ← v₁.val.map_one at a,
    rw ← v₂.val.map_one,
    intros r h,
    exact (heq r 1).mp (a.right r h) },
  { exact Valuation.is_continuous_of_equiv_is_continuous (setoid.symm heq) a.left },
  { rw ← v₁.val.map_one,
    rw ← v₂.val.map_one at a,
    intros r h,
    exact (heq r 1).mpr (a.right r h) },
end)

namespace Spa

variable {A : Huber_pair}

/-- basic open corresponding to r, s is v : v(r) <= v(s) and v(s) isn't 0 ( = v(0) ) -/
definition basic_open {A : Huber_pair} (r s : A) : set (Spa A) :=
Spv.lift (λ v : Valuation A, v r ≤ v s ∧ v s ≠ 0)
(λ v₁ v₂ heq,
begin
  ext, split; intro; split,
  { exact (heq r s).mp a.left },
  { exact Valuation.ne_zero_of_equiv_ne_zero heq a.right },
  { exact (heq r s).mpr a.left },
  { exact Valuation.ne_zero_of_equiv_ne_zero (setoid.symm heq) a.right }
end)
∘ subtype.val

instance (A : Huber_pair) : topological_space (Spa A) :=
topological_space.generate_from {U : set (Spa A) | ∃ r s : A, U = basic_open r s}

lemma basic_open.is_open {A : Huber_pair} (r s : A) : is_open (basic_open r s) :=
topological_space.generate_open.basic (basic_open r s) ⟨r, ⟨s, rfl⟩⟩

lemma basic_open_eq {A : Huber_pair} (s : A) : basic_open s s = {vs | ¬ vs.val.val s 0} :=
begin
  ext vs,
  split,
  { intro h,
    exact h.2 },
  { intro h,
    split, swap, exact h,
    rcases vs.val.property with ⟨Γ, ⟨inst, ⟨v, H⟩⟩⟩,
    simp [H] }
end

-- should only be applied with (HfinT : fintype T) and (Hopen: is_open (span T))
definition rational_open {A : Huber_pair} (s : A) (T : set A) : set (Spa A) :=
{vs | (∀ t ∈ T, (vs.val.val t s)) ∧ (¬ vs.val.val s 0)}

definition rational_open_Inter {A : Huber_pair} (s : A) (T : set A) :
rational_open s T = (set.Inter (λ (t : T), basic_open t s)) ∩ {vs | ¬ vs.val.val s 0} :=
set.ext $ λ vs, ⟨λ H, ⟨set.mem_Inter.2 $ λ t,⟨H.left _ t.property,H.right⟩,H.right⟩,
  λ ⟨H1,H2⟩,⟨λ t ht,(set.mem_Inter.1 H1 ⟨t, ht⟩).1,H2⟩⟩

lemma rational_open_add_s {A : Huber_pair} (s : A.R) (T : set A.R) :
rational_open s T = rational_open s (insert s T) :=
set.ext $ λ ⟨⟨r,Γ,HΓ,v,Hv⟩,_,_⟩, 
⟨ λ ⟨H1, H2⟩, ⟨λ t Ht, or.rec_on Ht (λ H, begin rw H, show r s s, rw Hv s s, end) (H1 t), H2⟩,
  λ ⟨H1, H2⟩, ⟨λ t Ht, H1 t $ set.mem_insert_of_mem _ Ht,H2⟩⟩

lemma rational_open.is_open {A : Huber_pair} (s : A) (T : set A) (HfinT : fintype T) :
is_open (rational_open s T) :=
begin
  rw rational_open_Inter,
  apply is_open_inter, swap, rw ← basic_open_eq s, exact basic_open.is_open s s,
  simpa using @is_open_bInter _ _ _ _ (λ t : T, basic_open t.1 s) 
    (finite_mem_finset finset.univ) (λ t ht, basic_open.is_open t s),
end

end Spa

-- goal now to define the 𝓞_X on *rational subsets* and then to extend.

-- to define it on rational subsets it's just a ring completion.

-- remember that a rational open is not actually `rational_open s T` in full
-- generality -- we also need that T is finite and that T generates an open ideal in A.
-- The construction on p73/74 (note typo in first line of p74 -- ideal should be I.D)
-- gives A<T/s> (need completion) and A<T/s>^+ (need integral closure).

-- Once we have this, we see mid way through p75 that the definition of the presheaf
-- on V is proj lim of O_X(U) as U runs through rationals opens in V. This gets
-- the projective limit topology and then we have a presheaf (hopefully this is
-- straightforward) of complete topological rings (need proj lim of complete is complete)

-- We then need the valuations on the stalks (this is direct limit in cat of rings, forget
-- the topology). This will be fiddly but not impossible.

-- We then have an object in V^pre and I think then everything should follow.