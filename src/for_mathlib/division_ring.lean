import algebra.field

-- Note(jmc): I think these simp lemmas should use coercions.
-- In that case the direction of the simp-lemma should probably be reversed.

-- @[simp]
-- lemma division_ring.val_inv {R : Type*} [division_ring R] (x : units R) : (x.val)⁻¹ = x.inv :=
-- begin
--   rw [←units.mul_left_inj x],
--   show x.val * _ = x.val * _,
--   rw [x.val_inv, mul_inv_cancel],
--   have h : x.val * x.inv ≠ 0,
--     rw x.val_inv,
--     simp,
--   exact ne_zero_of_mul_ne_zero_right h
-- end

-- @[simp]
-- lemma division_ring.inv_val {R : Type*} [division_ring R] (x : units R) : x⁻¹.val = x.inv := rfl

-- def units.mk' {R : Type*} [division_ring R] {y : R} (h : y ≠ 0) : units R :=
-- ⟨y, y⁻¹, mul_inv_cancel h, inv_mul_cancel h⟩
