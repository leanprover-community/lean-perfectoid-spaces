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

instance quotient.is_comm_ring : comm_ring (quotient R I) := {
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

instance quotient.is_ring : ring (quotient R I) := by apply_instance 

instance quotient.has_zero : has_zero (comm_ring.quotient R I) := by apply_instance 

instance quotient.mk_is_ring_hom : @is_ring_hom _ _ _ (quotient.is_ring I) (quotient.mk : R → quotient R I) := 
{ map_add := λ a b, rfl,
  map_mul := λ a b, rfl,
  map_one := rfl
}

variable (a : R)

@[simp] lemma quotient.zero (a : R) : a ∈ I ↔ (⟦a⟧ : quotient R I) = (0 : quotient R I) := 
  calc a ∈ I ↔ a - 0 ∈ I : by rw sub_zero
  ...        ↔ a ≈ 0 : begin have X := setoid.r a 0,sorry,end
  ...        ↔ ⟦a⟧ = ⟦0⟧ : by sorry
  ...        ↔ (⟦a⟧ : quotient R I) = (0 : quotient R I) : by sorry

variable {I} 

definition quotient.lift {S : Type} [comm_ring S] {f : R → S} [is_ring_hom f] (H : ∀ i : I, f i = 0) :
  quotient R I → S := quotient.lift f $ λ a b H1,
  begin
  rw is_submodule.quotient_rel_eq at H1,
  have H2 : ∃ i : I, a - b = i := by simpa using H1,
  cases H2 with i Hi,
  have H3 : f (a - b) = 0,
    rw Hi,
    exact H i,
  rw is_ring_hom.map_sub f at H3,
  exact eq_of_sub_eq_zero H3
  end

theorem quotient.universal_property {S : Type} [comm_ring S] {f : R → S} [is_ring_hom f] (H : ∀ i : I, f i = 0) :
  is_ring_hom (quotient.lift H) := 
{ map_add := λ a b, quotient.induction_on₂ a b $ λ a' b',
    begin show f (a' + b') = f a' + f b',exact is_ring_hom.map_add f,end,
  map_mul := λ a b, quotient.induction_on₂ a b $ λ a' b',
    begin show f (a' * b') = f a' * f b',exact is_ring_hom.map_mul f,end,
  map_one := begin show f 1 = 1,exact is_ring_hom.map_one f end
}

--set_option pp.implicit true
--set_option pp.all true
instance [HPI : is_prime_ideal I] : integral_domain (quotient R I) := 
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b,quotient.induction_on₂ a b $ λ a' b' (H : ⟦a' * b'⟧ = 0),begin
  have H2 : a' * b' ∈ I,
    unfold quotient.mk at H,
    -- testing
    let Htest : setoid R := (@quotient_rel R _inst_1 I _inst_2),
    let Htest_r := Htest.r,
    let Htest_rab := Htest_r a' b',
    
    trace_state,
    sorry,sorry
--    unfold comm_ring.quotient_rel I at H,
--    simp [H],
    end,
  zero_ne_one := sorry,
  ..quotient.is_comm_ring I,
}
end comm_ring