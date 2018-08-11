import valuation_spectrum
import continuous_valuations
import Huber_pair 

-- Wedhorn def 7.23.
definition Spa (A : Huber_pair) := {vs : Spv A.R // Spv.is_continuous vs ∧ ∀ r : A.R, r ∈ A.Rplus → vs.val r 1}

definition basic_open {A : Huber_pair} (r s : A.R) : set (Spa A) := 
{vs | vs.val.val r s ∧ ¬ vs.val.val s 0}

instance (A : Huber_pair) : topological_space (Spa A) :=
topological_space.generate_from {U : set (Spa A) | ∃ r s : A.R, U = basic_open r s}

-- should only be applied with (HFinT : fintype T) and (Hopen: is_open (span T))
definition rational_open {A : Huber_pair} (s : A.R) (T : set A.R) : set (Spa A) :=
{vs | (∀ t ∈ T, (vs.val.val t s)) ∧ (¬ vs.val.val s 0)}

definition rational_open_Inter {A : Huber_pair} (s : A.R) (T : set A.R) :
rational_open s T = (set.Inter (λ (t : T), basic_open t s)) ∩ {vs | ¬ vs.val.val s 0} :=
begin
  apply set.ext,
  intro vs,
  split,
    intro H,
    split,
      rw set.mem_Inter,intro t,
      split,
        exact H.left t.val t.property,
      exact H.right,
    exact H.right,
  intro H,
  cases H with H1 H2,
  rw set.mem_Inter at H1,
  split,
    intros t ht,
    exact (H1 ⟨t,ht⟩).left,
  exact H2
end

lemma rational_open_is_open {A : Huber_pair} (s : A.R) (T : set A.R) (HFinT : fintype T) :
is_open (rational_open s T) := sorry -- finite intersection of opens is open

-- goal now to define the 𝓞_X on *rational subsets*. 

