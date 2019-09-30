import ring_theory.power_series
import algebra.char_p

import adic_space

namespace power_series
variables {p : ℕ} [hp : p.prime]
variables {K : Type*} [discrete_field K] [char_p K p]

open_locale classical

noncomputable def valuation : valuation (power_series K) nnreal :=
{ to_fun := λ φ, if h : φ.order.dom then (p^(φ.order.get h))⁻¹ else 0,
  map_zero' := by { rw [dif_neg], rw [order_zero], exact not_false },
  map_one' := by { rw [dif_pos]; simp, },
  map_mul' := λ x y,
  begin
    by_cases hx : x.order.dom,
    { by_cases hy : y.order.dom,
      { have hxy' : (x.order + y.order).dom := ⟨hx, hy⟩,
        have hxy : (x*y).order.dom, { rwa order_mul },
        rw [dif_pos hxy, dif_pos hx, dif_pos hy],
        rw [subtype.coe_ext, nnreal.coe_inv, nnreal.coe_mul, nnreal.coe_inv, nnreal.coe_inv],
        rw [← mul_inv', ← nnreal.coe_mul, ← pow_add, add_comm, ← enat.get_add],
        { congr, rw [order_mul] },
        { exact hxy' } },
      { rw [dif_pos hx, dif_neg hy, dif_neg, mul_zero],
        rw order_mul, contrapose! hy with H, exact H.2 } },
    { rw [dif_neg hx, dif_neg, zero_mul],
      rw order_mul, contrapose! hx with H, exact H.1 },
  end,
  map_add' := λ x y,
  begin
    have := order_add_ge x y,
    by_cases hxy : (x + y).order.dom,
    { rw dif_pos hxy, sorry },
    { rw dif_neg hxy, exact zero_le _ }
  end }

end power_series
