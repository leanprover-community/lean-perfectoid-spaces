import valuation_spectrum
import continuous_valuations
import Huber_pair 

open set

-- Wedhorn def 7.23.
definition Spa (A : Huber_pair) := {vs : Spv A | Spv.is_continuous vs ∧ ∀ r, r ∈ A⁺ → vs.val r 1}

/-- basic open corresponding to r, s is v : v(r) <= v(s) and v(s) isn't 0 ( = v(0) ) -/
definition basic_open {A : Huber_pair} (r s : A) : set (Spa A) :=
{vs | vs.val.val r s ∧ ¬ vs.val.val s 0}

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

/- this used to say 
begin
  intro x,
  split,
  { intro Hx,
    split,
      intro t,
      intro Ht,
      cases Ht,
        rw Ht,
        rcases x.val.property with ⟨Γ,_,v,Hv⟩,
        rw Hv s s,
      exact Hx.1 t Ht,
    exact Hx.2
  },
  { intro Hx,
    split,
      intros t Ht,
      refine Hx.1 t _,
      exact set.mem_insert_of_mem _ Ht,
    exact Hx.2
  }
end

and then I golfed it. 
-/

-- set.ext $ λ x, ⟨λ Hx,⟨λ t Ht,Hx.1 t (_),_⟩,_⟩ -- made a start then ran out of time

lemma rational_open.is_open {A : Huber_pair} (s : A) (T : set A) (HfinT : fintype T) :
is_open (rational_open s T) :=
begin
  rw rational_open_Inter,
  apply is_open_inter, swap, rw ← basic_open_eq s, exact basic_open.is_open s s,
  simpa using @is_open_bInter _ _ _ _ (λ t : T, basic_open t.1 s) 
    (finite_mem_finset finset.univ) (λ t ht, basic_open.is_open t s),
end

-- goal now to define the 𝓞_X on *rational subsets* and then to extend.

