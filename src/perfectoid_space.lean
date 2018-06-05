-- definitions of adic_space, preadic_space, Huber_pair etc
import adic_space 

--notation
postfix `ᵒ` : 66 := power_bounded_subring

/-- A perfectoid ring, following Fontaine Sem Bourb-/
class perfectoid_ring (p : ℕ) [is_prime p] (R : Type) extends Tate_ring R :=
(is_complete : complete R)
(is_uniform  : uniform R)
(ramified    : ∃ ϖ : Rᵒ, (is_pseudo_uniformizer ϖ) ∧ (ϖ ^ p ∣ p))
(Frob        : ∀ a : Rᵒ, ∃ b : Rᵒ, (p : Rᵒ) ∣ (b ^ p - a))

structure perfectoid_cover (p : ℕ) [is_prime p] (X : Type) [adic_space X] :=
(𝓤 : set (set X))
[𝓤_open : ∀ U ∈ 𝓤, is_open U]
(𝓤_cover : ∀ x : X, ∃ U ∈ 𝓤, x ∈ U)
(𝓤_affinoid_perfectoid : ∀ U ∈ 𝓤, ∃ (A : Huber_pair) (Aperf : perfectoid_ring p A),
  is_preadic_space_equiv (preadic_space_pullback U) (Spa A)  )      

class perfectoid_space (p : ℕ) [is_prime p] (X : Type) extends adic_space X :=
(exists_perfectoid_cover : perfectoid_cover p X)
