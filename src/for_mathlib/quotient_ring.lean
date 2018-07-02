/-
Copyright (c) 2018 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard

Quotient rings
-/
import linear_algebra.quotient_module
import ring_theory.ideals
import data.set.function

namespace comm_ring

variables {R : Type} (I : set R)
variables [comm_ring R] [is_ideal I]

def quotient_rel (I : set R) [is_ideal I] : setoid R := is_submodule.quotient_rel I

local attribute [instance] quotient_rel

def quotient (R : Type) (I : set R) [comm_ring R] [is_ideal I] : Type :=
quotient (quotient_rel I)

instance quotient.has_one : has_one (quotient R I) := ⟨⟦ 1 ⟧⟩

-- why doesn't namespace quotient; instance has_mul work?

instance quotient.has_mul : has_mul (quotient R I) :=
⟨λ a b, quotient.lift_on₂ a b (λ a b, ⟦a * b⟧)
  (λ a₁ b₁ a₂ b₂ (Ha : a₁ - a₂ ∈ I) (Hb : b₁ - b₂ ∈ I),
  quotient.sound begin
    show a₁ * b₁ - a₂ * b₂ ∈ I,
    have H₁ : a₁ * b₁ - a₂ * b₂ = a₁ * (b₁ - b₂) + (a₁ - a₂) * b₂,
      simp [mul_add,add_mul],
    have H₂ : a₁ * (b₁ - b₂) ∈ I := is_submodule.smul a₁ Hb,
    have H₃ : (a₁ - a₂) * b₂ ∈ I := mul_comm b₂ (a₁ - a₂) ▸ is_submodule.smul b₂ Ha,
    rw H₁,
    exact is_submodule.add H₂ H₃
  end)⟩

instance : comm_ring (quotient R I) := {
  mul := (*),
  mul_assoc := assume a b c, quotient.induction_on₃ a b c $ assume a' b' c', quotient.sound $
    by rw mul_assoc;refl,
  one := 1,
  one_mul := λ a, quotient.induction_on a $ λ a', quotient.sound $ by simp,
  mul_one := λ a, quotient.induction_on a $ λ a', quotient.sound $ by simp,
  left_distrib := λ a b c, quotient.induction_on₃ a b c $ λ a' b' c', quotient.sound $
    by simp [mul_add],
--    by simp [left_distrib], -- fails!
  right_distrib := λ a b c, quotient.induction_on₃ a b c $ λ a' b' c', quotient.sound $
    by simp [add_mul],
  mul_comm := λ a b, quotient.induction_on₂ a b $ λ a' b', quotient.sound $
    by simp [mul_comm],
  ..is_submodule.quotient.add_comm_group I
}

variable {I} 

definition quotient.universal_map {S : Type} [comm_ring S] {f : R → S} (H : I ⊆ f ⁻¹' {0}) :
  quotient R I → S := sorry 

theorem quotient.universal_property {S : Type} [comm_ring S] {f : R → S} (H : I ⊆ f ⁻¹' {0}) :
  is_ring_hom (quotient.universal_map H) := sorry

instance [is_prime_ideal I] : integral_domain (quotient R I) := sorry

end comm_ring