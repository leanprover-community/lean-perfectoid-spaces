import valuation_spectrum
import continuous_valuations
import Huber_pair 

-- Wedhorn def 7.23.
definition Spa (A : Huber_pair) := {vs : Spv A.R // Spv.is_continuous vs ∧ ∀ r : A.R, r ∈ A.Rplus → vs.val r 1}

/-- basic open corresponding to r, s is v : v(r) <= v(s) and v(s) isn't 0 ( = v(0) ) -/
definition basic_open {A : Huber_pair} (r s : A.R) : set (Spa A) := 
{vs | vs.val.val r s ∧ ¬ vs.val.val s 0}

instance (A : Huber_pair) : topological_space (Spa A) :=
topological_space.generate_from {U : set (Spa A) | ∃ r s : A.R, U = basic_open r s}

-- should only be applied with (HFinT : fintype T) and (Hopen: is_open (span T))
definition rational_open {A : Huber_pair} (s : A.R) (T : set A.R) : set (Spa A) :=
{vs | (∀ t ∈ T, (vs.val.val t s)) ∧ (¬ vs.val.val s 0)}

theorem rational_open_Inter {A : Huber_pair} (s : A.R) (T : set A.R) :
rational_open s T = (set.Inter (λ (t : T), basic_open t s)) ∩ {vs | ¬ vs.val.val s 0} :=
set.ext $ λ vs, ⟨λ H, ⟨set.mem_Inter.2 $ λ t,⟨H.left _ t.property,H.right⟩,H.right⟩,
  λ ⟨H1,H2⟩,⟨λ t ht,(set.mem_Inter.1 H1 ⟨t, ht⟩).1,H2⟩⟩

lemma rational_open_add_s {A : Huber_pair} (s : A.R) (T : set A.R) :
rational_open s T = rational_open s (insert s T) := sorry
-- set.ext $ λ x, ⟨λ Hx,⟨λ t Ht,Hx.1 t (_),_⟩,_⟩ -- made a start then ran out of time

lemma rational_open_is_open {A : Huber_pair} (s : A.R) (T : set A.R) (HFinT : fintype T) :
is_open (rational_open s T) := begin
  rw rational_open_Inter,
  sorry -- should hopefully be easy, if I've got it right.
end

-- goal now to define the 𝓞_X on *rational subsets* and then to extend.

