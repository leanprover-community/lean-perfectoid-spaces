import Huber_ring 

universe u


section topological_ring
variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]  

/-- Wedhorn Definition 5.27 page 36 -/
definition is_bounded 
  (B : set R) : Prop := ∀ U ∈ (nhds (0 :R)).sets, ∃ V ∈ (nhds (0 :R)).sets, ∀ v ∈ V, ∀ b ∈ B, v*b ∈ U

definition is_power_bounded (r : R) : Prop := is_bounded (powers r)

variable (R)
definition power_bounded_subring := {r : R | is_power_bounded r}

instance power_bounded_subring_to_ring : has_coe (power_bounded_subring R) R := ⟨subtype.val⟩ 
instance power_bounded_subring_is_ring  : comm_ring (power_bounded_subring R) := sorry
instance : topological_space (power_bounded_subring R) := subtype.topological_space
instance : topological_ring (power_bounded_subring R) := sorry

definition is_uniform : Prop := is_bounded (power_bounded_subring R)


variable {R}
definition is_pseudo_uniformizer : R → Prop := sorry

-- definition power (R : Type) [comm_ring R] (n : ℕ) (I : set R) [is_ideal I] := I ^ n 

--definition Iadic_topology {R : Type*} [comm_ring R] (I : set R) [is_ideal I] : topological_space R :=
--topological_space.generate_from {U : set R | ∃ (n : ℕ) (r : R), U = r + I ^ n } 

end topological_ring



-- Wedhorn Def 7.14
structure is_ring_of_integral_elements {R : Type u} [Huber_ring R] (Rplus : set R) : Prop :=
[is_subring : is_subring Rplus]
(is_open : is_open Rplus)
(is_int_closed : is_integrally_closed Rplus)
(is_power_bounded : Rplus ⊆ { r : R | is_power_bounded r})

-- a Huber Ring is an f-adic ring.
-- a Huber Pair is what Huber called an Affinoid Ring.
structure Huber_pair :=
(R : Type u) 
[RHuber : Huber_ring R]
(Rplus : set R)
[intel : is_ring_of_integral_elements Rplus]

instance : has_coe_to_sort Huber_pair := 
{ S := Type, coe := Huber_pair.R}

instance Huber_pair.Huber_ring (A : Huber_pair) : Huber_ring A.R := A.RHuber 

postfix `⁺` : 66 := λ R : Huber_pair _, R.Rplus  
