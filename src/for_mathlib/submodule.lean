import ring_theory.noetherian
import ring_theory.algebra_operations

local attribute [instance] classical.prop_decidable

variables {R : Type*} [comm_ring R]
variables (I J : ideal R)

open finset

lemma fg_mul (h₁ : I.fg) (h₂ : J.fg) : (I * J).fg :=
begin
  cases h₁ with s₁ hs₁,
  cases h₂ with s₂ hs₂,
  let s : finset R := s₁.bind (λ r₁, s₂.image $ (λ r₂, r₁ * r₂)),
  use s,
  erw [← hs₁, ← hs₂, ideal.span_mul_span],
  congr' 1,
  ext,
  erw [mem_bind, set.mem_bUnion_iff],
  apply exists_congr,
  intro r₁,
  rw exists_prop,
  apply and_congr iff.rfl,
  erw [mem_image, set.mem_bUnion_iff],
  apply exists_congr,
  intro r₂,
  rw set.mem_singleton_iff,
  rw exists_prop,
  apply and_congr iff.rfl,
  tauto
end

lemma fg_pow (h : I.fg) (n : ℕ) : (I^n).fg :=
begin
  induction n with n ih,
  { refine ⟨finset.singleton 1, _⟩,
    erw [ideal.span_singleton_eq_top],
    exact is_unit_one },
  { erw pow_succ,
    apply fg_mul; assumption }
end


-- This doesn't work yet, because submodules of an algebra do not yet form a monoid
-- variables {A : Type*} [ring A] [algebra R A]
-- variables (M : submodule R A)

-- lemma fg_pow (h : M.fg) (n : ℕ) : (M^n).fg := _
