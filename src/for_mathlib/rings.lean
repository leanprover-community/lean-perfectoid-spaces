import ring_theory.ideal_operations ring_theory.localization data.equiv.algebra
import for_mathlib.subtype

universes u u₁ u₂ v

namespace ideal
open function

@[simp] lemma map_quotient_self {R : Type u} [comm_ring R] (I : ideal R) :
  ideal.map (ideal.quotient.mk I) I = ⊥ :=
lattice.eq_bot_iff.2 $ ideal.map_le_iff_le_comap.2 $
begin
  intros x hx,
  erw submodule.mem_bot I.quotient,
  exact ideal.quotient.eq_zero_iff_mem.2 hx, apply_instance
end

lemma eq_bot_or_top {K : Type u} [discrete_field K] (I : ideal K) :
  I = ⊥ ∨ I = ⊤ :=
begin
  rw classical.or_iff_not_imp_right,
  change _ ≠ _ → _,
  rw ideal.ne_top_iff_one,
  intro h1,
  apply le_antisymm, swap, exact lattice.bot_le,
  intros r hr,
  by_cases H : r = 0,
  simpa,
  simpa [H, h1] using submodule.smul_mem I r⁻¹ hr,
end

lemma eq_bot_of_prime {K : Type u} [discrete_field K] (I : ideal K) [h : I.is_prime] :
  I = ⊥ :=
classical.or_iff_not_imp_right.mp I.eq_bot_or_top h.1

-- This should just be the conjunction of
-- comap f ⊥ = ker f
-- ker f = ⊥  (for injective f)
lemma comap_bot_of_inj {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] (f : R → S) [is_ring_hom f]
(h : injective f) :
  ideal.comap f ⊥ = ⊥ :=
lattice.eq_bot_iff.2 $
begin
  intros r hr,
  change r ∈ f ⁻¹' {0} at hr,
  simp at *,
  apply h,
  rw hr,
  symmetry,
  rw is_ring_hom.map_zero f,
end

end ideal

-- Everything that follows is currently being PR'd to mathlib

section
open localization
variables (A : Type*) [integral_domain A]
@[simp] lemma non_zero_divisors_one_val :  (1 : non_zero_divisors A).val = 1 := rfl

end

namespace localization
open function is_ring_hom localization
variables {A : Type u} [integral_domain A] [decidable_eq A]
variables {B : Type v} [integral_domain B] [decidable_eq B]
variables (f : A → B) [is_ring_hom f]

def map (hf : injective f) : fraction_ring A → fraction_ring B :=
quotient.lift (λ rs : A × (non_zero_divisors A), (f rs.1 : fraction_ring B) / (f rs.2.val)) $
λ x y hxy,
begin
  erw div_eq_div_iff,
  { rcases hxy with ⟨t, ht, H⟩,
    replace H := ht _ H,
    rw sub_eq_zero at H,
    erw [← coe_mul, ← coe_mul, ← map_mul f, ← map_mul f],
    congr' 2,
    convert H.symm using 1; exact mul_comm _ _, },
    all_goals { intro h,
      rw [← coe_zero, ← map_zero f] at h,
      exact ne_zero_of_mem_non_zero_divisors (by simp) (injective_comp of.injective hf h), },
end

@[simp] lemma map_coe (hf : injective f) (a : A) : map f hf a = f a :=
begin
  delta map,
  erw quotient.lift_beta,
  simp [map_one f],
end

@[simp] lemma map_of (hf : injective f) (a : A) : map f hf (of a) = of (f a) :=
begin
  delta map,
  erw quotient.lift_beta,
  simpa [map_one f],
end

@[simp] lemma map_mk (hf : injective f) (x : A × (non_zero_divisors A)) :
  map f hf ⟦x⟧ = (f x.1) / (f x.2.val) := rfl

@[simp] lemma map_circ_of (hf : injective f) :
  map f hf ∘ (of : A → fraction_ring A) = (of : B → fraction_ring B) ∘ f :=
funext $ map_of f hf

instance map.is_field_hom (hf : injective f) : is_field_hom (map f hf) :=
{ map_one := by erw [map_of f hf 1, map_one f]; refl,
  map_mul :=
  begin
    rintros ⟨x⟩ ⟨y⟩,
    repeat {erw map_mk},
    rw div_mul_div,
    congr' 1; erw [map_mul f, coe_mul],
  end,
  map_add :=
  begin
    rintros ⟨x⟩ ⟨y⟩,
    repeat {erw map_mk},
    rw div_add_div,
    { congr' 1,
      { simp only [coe_mul, coe_add, map_mul f, map_add f],
        unfold_coes,
        ring, },
      { erw [← coe_mul, ← map_mul f],
        refl, } },
    all_goals { intro h,
      rw [← coe_zero, ← map_zero f] at h,
      exact ne_zero_of_mem_non_zero_divisors (by simp) (injective_comp of.injective hf h), },
  end }

def equiv_of_equiv (h : A ≃r B) : fraction_ring A ≃r fraction_ring B :=
{ hom := by apply_instance,
  to_fun := map h.to_equiv (injective_of_left_inverse h.left_inv),
  inv_fun := map h.symm.to_equiv (injective_of_left_inverse h.symm.left_inv),
  left_inv :=
  begin
    rintro ⟨x⟩,
    erw [map_mk, is_field_hom.map_div (map _ _)],
    { simp only [map_coe],
      repeat {erw h.to_equiv.inverse_apply_apply},
      symmetry, erw ← mk_eq_div; cases x; refl },
    apply_instance
  end,
  right_inv :=
  begin
    rintro ⟨x⟩,
    erw [map_mk, is_field_hom.map_div (map _ _)],
    { simp only [map_coe],
      repeat {erw h.to_equiv.apply_inverse_apply},
      symmetry, erw ← mk_eq_div; cases x; refl },
    apply_instance
end }

end localization
