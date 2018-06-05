-- definitions of adic_space, preadic_space, Huber_pair etc
import adic_space 

--notation
postfix `ᵒ` : 66 := power_bounded_subring

/-- A perfectoid ring, following Fontaine Sem Bourb-/
class perfectoid_ring (R : Type) (p : ℕ) [is_prime p] extends Tate_ring R :=
(is_complete : complete R)
(is_uniform  : uniform R)
(ramified    : ∃ ω : R ᵒ, (is_pseudo_uniformizer ω) ∧ (ω ^ p ∣ p))
(Frob        : ∀ a : R ᵒ, ∃ b : R ᵒ, (p : R ᵒ) ∣ (b ^ p - a))

structure perfectoid_space (X : Type) (p : ℕ) [is_prime p] extends adic_space X :=
(perfectoid_cover : 
  -- gamma is our indexing set, U_i are the open cover for i in gamma
  ∃ (γ : Type) (U : γ → set X) [Uopen : ∀ i, is_open (U i)] (U_cover : is_cover U)
  -- U i is isomorphic to Spa(A_i,A_i^+) with A_i a perfectoid ring
  (A : γ → Huber_pair) (is_perfectoid : ∀ i, perfectoid_ring (A i) p),
  ∀ i, is_preadic_space_equiv (U i) (Spa (A i))    ) 
